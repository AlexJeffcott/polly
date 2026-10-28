// Evaluator for the parsed subset. `evaluate` gives a value. `enumerate` walks
// an action as TLC does and calls `k` once for each way the action holds:
//   * A /\ B   : A, then B with A's assignments
//   * A \/ B   : A, then B (each successor counts, duplicates too)
//   * \E x \in S : A : A once for each x
//   * x' = e   : assigns x' when it is not yet assigned, else compares
//   * x' \in S : one branch per element when x' is not yet assigned
//   * UNCHANGED v : v' = v for each variable in v
//   * IF c THEN A ELSE B : c is evaluated, then one branch
//   * any other conjunct : a guard
// In Init the same rules apply to unprimed variables.

import type { Bound, Def, Expr } from "./parser";
import {
  apply, describe, elements, EvalError, equal, key, Lazy, member, mkRecord, mkSeq, mkSet,
  type SetValue, seqItems, show, TFun, TSet, type Value,
} from "./values";

export class Closure {
  cache?: Value;
  constructor(
    readonly def: Def,
    readonly env: Env
  ) {}
}
type Binding = Value | Closure;
export type Env = { name: string; b: Binding; up: Env } | null;

export type Ctx = {
  cur: Array<Value | undefined>;
  nxt: Array<Value | undefined>;
  primed: boolean;
  init: boolean;
  env: Env;
  at?: Value;
  // TLCGet("level") of the state being checked: init states are level 1.
  level?: number;
};

const BUILTIN_SETS = new Set(["Nat", "Int", "STRING", "BOOLEAN"]);
const BUILTIN_OPS = new Set([
  "Len", "Append", "Head", "Tail", "SubSeq", "Seq", "Cardinality", "IsFiniteSet", "Print", "Assert", "ToString",
  "TLCGet",
]);

function lookupEnv(env: Env, name: string): Binding | undefined {
  for (let e = env; e; e = e.up) if (e.name === name) return e.b;
  return undefined;
}

export class Evaluator {
  readonly varIndex: Map<string, number>;
  private readonly constantDefs = new Map<string, Value>();
  private readonly constantLevel = new Map<string, boolean>();

  constructor(
    readonly defs: Map<string, Def>,
    readonly constants: Map<string, Value>,
    readonly vars: string[]
  ) {
    this.varIndex = new Map(vars.map((v, i) => [v, i]));
  }

  // A definition with no parameters whose body reads no variable is
  // evaluated once.
  private isConstantLevel(name: string, seen = new Set<string>()): boolean {
    const cached = this.constantLevel.get(name);
    if (cached !== undefined) return cached;
    if (seen.has(name)) return false;
    seen.add(name);
    const def = this.defs.get(name);
    if (!def) return true;
    let ok = true;
    const walk = (e: unknown): void => {
      if (!ok || e === null || typeof e !== "object") return;
      if (Array.isArray(e)) {
        for (const x of e) walk(x);
        return;
      }
      const node = e as Expr;
      if (node.k === "prime" || (node.k === "op" && (node.op === "ENABLED" || node.op === "UNCHANGED"))) ok = false;
      else if (node.k === "id" || node.k === "call") {
        if (this.varIndex.has(node.name)) ok = false;
        else if (this.defs.has(node.name) && !this.isConstantLevel(node.name, seen)) ok = false;
      }
      for (const v of Object.values(node)) walk(v);
    };
    walk(def.body);
    this.constantLevel.set(name, ok);
    return ok;
  }

  private bool(e: Expr, ctx: Ctx): boolean {
    const v = this.evaluate(e, ctx);
    if (typeof v !== "boolean") throw new EvalError(`expected a boolean, got ${show(v)}`);
    return v;
  }
  private num(e: Expr, ctx: Ctx): number {
    const v = this.evaluate(e, ctx);
    if (typeof v !== "number") throw new EvalError(`expected a number, got ${show(v)}`);
    return v;
  }
  private set(e: Expr, ctx: Ctx): SetValue {
    const v = this.evaluate(e, ctx);
    if (!(v instanceof TSet || v instanceof Lazy)) throw new EvalError(`expected a set, got ${show(v)}`);
    return v;
  }

  private readVar(i: number, name: string, ctx: Ctx): Value {
    const v = ctx.primed ? ctx.nxt[i] : ctx.cur[i];
    if (v === undefined) throw new EvalError(`${name}${ctx.primed ? "'" : ""} is read before it is assigned`);
    return v;
  }

  private callDef(def: Def, env: Env, args: Value[], ctx: Ctx): Ctx {
    if (args.length !== def.params.length) throw new EvalError(`${def.name} takes ${def.params.length} arguments`);
    let e = env;
    for (let i = 0; i < args.length; i++) e = { name: def.params[i] as string, b: args[i] as Value, up: e };
    return { ...ctx, env: e, at: undefined };
  }

  // The definition an identifier or call names, if it is a user definition.
  private resolveDef(name: string, ctx: Ctx): { def: Def; env: Env; closure?: Closure } | undefined {
    const bound = lookupEnv(ctx.env, name);
    if (bound !== undefined) return bound instanceof Closure ? { def: bound.def, env: bound.env, closure: bound } : undefined;
    if (this.varIndex.has(name) || this.constants.has(name)) return undefined;
    const def = this.defs.get(name);
    return def ? { def, env: null } : undefined;
  }

  evaluate(e: Expr, ctx: Ctx): Value {
    switch (e.k) {
      case "num":
      case "str":
      case "bool":
        return e.v;
      case "id":
        return this.ident(e.name, ctx);
      case "call":
        return this.call(e.name, e.args, ctx);
      case "op":
        return this.op(e.op, e.args, ctx);
      case "and":
        for (const x of e.items) if (!this.bool(x, ctx)) return false;
        return true;
      case "or":
        for (const x of e.items) if (this.bool(x, ctx)) return true;
        return false;
      case "prime":
        if (ctx.primed) throw new EvalError("a prime inside a prime");
        return this.evaluate(e.e, { ...ctx, primed: true });
      case "index": {
        const f = this.evaluate(e.f, ctx);
        const args = e.args.map((a) => this.evaluate(a, ctx));
        return apply(f, args.length === 1 ? (args[0] as Value) : mkSeq(args));
      }
      case "dot":
        return apply(this.evaluate(e.r, ctx), e.field);
      case "setEnum":
        return mkSet(e.items.map((x) => this.evaluate(x, ctx)));
      case "setFilter": {
        const out: Value[] = [];
        for (const v of elements(this.set(e.set, ctx))) {
          if (this.bool(e.pred, { ...ctx, env: { name: e.v, b: v, up: ctx.env } })) out.push(v);
        }
        return mkSet(out);
      }
      case "setMap": {
        const out: Value[] = [];
        this.bind(e.bounds, ctx, (c) => {
          out.push(this.evaluate(e.e, c));
          return false;
        });
        return mkSet(out);
      }
      case "tuple":
        return mkSeq(e.items.map((x) => this.evaluate(x, ctx)));
      case "fun": {
        const [b] = e.bounds;
        if (e.bounds.length !== 1 || !b || b.vars.length !== 1) throw new EvalError("[x \\in S, y \\in T |-> e] is not supported");
        const name = b.vars[0] as string;
        const dom = elements(this.set(b.set, ctx));
        return new TFun(dom, dom.map((v) => this.evaluate(e.e, { ...ctx, env: { name, b: v, up: ctx.env } })));
      }
      case "rec":
        return mkRecord(e.fields.map(([n, x]) => [n, this.evaluate(x, ctx)]));
      case "recSet":
        return new Lazy({ lazy: "recSet", fields: e.fields.map(([n, x]) => [n, this.set(x, ctx)]) });
      case "funSet":
        return new Lazy({ lazy: "funSet", dom: this.set(e.dom, ctx), range: this.set(e.range, ctx) });
      case "except": {
        let f = this.evaluate(e.f, ctx);
        for (const clause of e.clauses) f = this.update(f, clause.path, 0, clause.value, ctx);
        return f;
      }
      case "at":
        if (ctx.at === undefined) throw new EvalError("@ outside EXCEPT");
        return ctx.at;
      case "if":
        return this.bool(e.c, ctx) ? this.evaluate(e.t, ctx) : this.evaluate(e.e, ctx);
      case "let":
        return this.evaluate(e.body, this.letCtx(e.defs, ctx));
      case "choose": {
        for (const v of elements(this.set(e.set, ctx))) {
          if (this.bool(e.pred, { ...ctx, env: { name: e.v, b: v, up: ctx.env } })) return v;
        }
        throw new EvalError("CHOOSE found no element");
      }
      case "quant": {
        if (e.q === "E") return this.bind(e.bounds, ctx, (c) => this.bool(e.body, c));
        return !this.bind(e.bounds, ctx, (c) => !this.bool(e.body, c));
      }
      case "actBox":
      case "temporal":
        throw new EvalError("a temporal formula in a safety check");
    }
  }

  private letCtx(defs: Def[], ctx: Ctx): Ctx {
    let env = ctx.env;
    for (const d of defs) env = { name: d.name, b: new Closure(d, env), up: env };
    return { ...ctx, env };
  }

  // Calls fn for each binding of the bounds; stops and returns true when fn does.
  private bind(bounds: Bound[], ctx: Ctx, fn: (c: Ctx) => boolean): boolean {
    const flat: Array<{ name: string; set: Expr }> = [];
    for (const b of bounds) for (const v of b.vars) flat.push({ name: v, set: b.set });
    const go = (i: number, c: Ctx): boolean => {
      if (i === flat.length) return fn(c);
      const { name, set } = flat[i] as { name: string; set: Expr };
      for (const v of elements(this.set(set, c))) {
        if (go(i + 1, { ...c, env: { name, b: v, up: c.env } })) return true;
      }
      return false;
    };
    return go(0, ctx);
  }

  private update(f: Value, path: Array<{ index: Expr[] } | { field: string }>, i: number, value: Expr, ctx: Ctx): Value {
    if (i === path.length) return this.evaluate(value, { ...ctx, at: f });
    if (!(f instanceof TFun)) throw new EvalError(`EXCEPT on a ${describe(f)}`);
    const step = path[i] as { index: Expr[] } | { field: string };
    let k: Value;
    if ("field" in step) k = step.field;
    else {
      const args = step.index.map((a) => this.evaluate(a, ctx));
      k = args.length === 1 ? (args[0] as Value) : mkSeq(args);
    }
    const j = f.map.get(key(k));
    if (j === undefined) return f; // TLA+: EXCEPT outside the domain leaves f unchanged
    const val = f.val.slice();
    val[j] = this.update(f.val[j] as Value, path, i + 1, value, ctx);
    return new TFun(f.dom, val);
  }

  private ident(name: string, ctx: Ctx): Value {
    const bound = lookupEnv(ctx.env, name);
    if (bound !== undefined) {
      if (!(bound instanceof Closure)) return bound;
      if (bound.def.params.length > 0) throw new EvalError(`${name} needs arguments`);
      if (!ctx.primed && bound.cache !== undefined) return bound.cache;
      const v = this.evaluate(bound.def.body, { ...ctx, env: bound.env, at: undefined });
      if (!ctx.primed) bound.cache = v;
      return v;
    }
    const vi = this.varIndex.get(name);
    if (vi !== undefined) return this.readVar(vi, name, ctx);
    const c = this.constants.get(name);
    if (c !== undefined) return c;
    const def = this.defs.get(name);
    if (def) {
      if (def.params.length > 0) throw new EvalError(`${name} needs arguments`);
      if (this.isConstantLevel(name)) {
        let v = this.constantDefs.get(name);
        if (v === undefined) {
          v = this.evaluate(def.body, { ...ctx, env: null, at: undefined });
          this.constantDefs.set(name, v);
        }
        return v;
      }
      return this.evaluate(def.body, { ...ctx, env: null, at: undefined });
    }
    switch (name) {
      case "Nat":
      case "Int":
      case "STRING":
        return new Lazy({ lazy: name });
      case "BOOLEAN":
        return mkSet([false, true]);
    }
    throw new EvalError(`unknown identifier ${name}`);
  }

  private call(name: string, argExprs: Expr[], ctx: Ctx): Value {
    const target = this.resolveDef(name, ctx);
    if (target) {
      const args = argExprs.map((a) => this.evaluate(a, ctx));
      return this.evaluate(target.def.body, this.callDef(target.def, target.env, args, ctx));
    }
    if (!BUILTIN_OPS.has(name)) throw new EvalError(`unknown operator ${name}`);
    const args = argExprs.map((a) => this.evaluate(a, ctx));
    const [a, b, c] = args as [Value, Value, Value];
    switch (name) {
      case "Len":
        return typeof a === "string" ? a.length : seqItems(a).length;
      case "Append":
        return mkSeq([...seqItems(a), b]);
      case "Head": {
        const items = seqItems(a);
        if (items.length === 0) throw new EvalError("Head of an empty sequence");
        return items[0] as Value;
      }
      case "Tail": {
        const items = seqItems(a);
        if (items.length === 0) throw new EvalError("Tail of an empty sequence");
        return mkSeq(items.slice(1));
      }
      case "SubSeq": {
        if (typeof b !== "number" || typeof c !== "number") throw new EvalError("SubSeq needs numbers");
        if (typeof a === "string") return a.slice(b - 1, Math.max(b - 1, c));
        const items = seqItems(a);
        if (b > c) return mkSeq([]);
        if (b < 1 || c > items.length) throw new EvalError(`SubSeq(${show(a)}, ${b}, ${c}) is out of range`);
        return mkSeq(items.slice(b - 1, c));
      }
      case "Seq":
        if (!(a instanceof TSet || a instanceof Lazy)) throw new EvalError("Seq needs a set");
        return new Lazy({ lazy: "Seq", of: a });
      case "Cardinality":
        return elements(a).length;
      case "IsFiniteSet":
        return a instanceof TSet;
      case "Print":
        return b;
      case "Assert":
        if (a !== true) throw new EvalError(`Assert failed: ${show(b)}`);
        return true;
      case "ToString":
        return show(a);
      case "TLCGet":
        if (a !== "level") throw new EvalError(`TLCGet(${show(a)}) is not supported`);
        if (ctx.level === undefined) throw new EvalError("TLCGet(\"level\") outside a state check");
        return ctx.level;
    }
    throw new EvalError(`unknown operator ${name}`);
  }

  private op(op: string, args: Expr[], ctx: Ctx): Value {
    const [x, y] = args as [Expr, Expr];
    switch (op) {
      case "=":
        return equal(this.evaluate(x, ctx), this.evaluate(y, ctx));
      case "#":
        return !equal(this.evaluate(x, ctx), this.evaluate(y, ctx));
      case "<":
        return this.num(x, ctx) < this.num(y, ctx);
      case ">":
        return this.num(x, ctx) > this.num(y, ctx);
      case "<=":
        return this.num(x, ctx) <= this.num(y, ctx);
      case ">=":
        return this.num(x, ctx) >= this.num(y, ctx);
      case "+":
        return this.num(x, ctx) + this.num(y, ctx);
      case "-":
        return this.num(x, ctx) - this.num(y, ctx);
      case "*":
        return this.num(x, ctx) * this.num(y, ctx);
      case "%": {
        const a = this.num(x, ctx);
        const b = this.num(y, ctx);
        return ((a % b) + b) % b;
      }
      case "\\div":
        return Math.floor(this.num(x, ctx) / this.num(y, ctx));
      case "neg":
        return -this.num(x, ctx);
      case "~":
        return !this.bool(x, ctx);
      case "=>":
        return !this.bool(x, ctx) || this.bool(y, ctx);
      case "<=>":
        return this.bool(x, ctx) === this.bool(y, ctx);
      case "\\in":
        return member(this.evaluate(x, ctx), this.evaluate(y, ctx));
      case "\\notin":
        return !member(this.evaluate(x, ctx), this.evaluate(y, ctx));
      case "\\subseteq": {
        const b = this.evaluate(y, ctx);
        return elements(this.set(x, ctx)).every((v) => member(v, b));
      }
      case "\\union":
        return mkSet([...elements(this.set(x, ctx)), ...elements(this.set(y, ctx))]);
      case "\\intersect": {
        const b = this.set(y, ctx);
        return mkSet(elements(this.set(x, ctx)).filter((v) => member(v, b)));
      }
      case "\\": {
        const b = this.set(y, ctx);
        return mkSet(elements(this.set(x, ctx)).filter((v) => !member(v, b)));
      }
      case "..": {
        const lo = this.num(x, ctx);
        const hi = this.num(y, ctx);
        const out: number[] = [];
        for (let i = lo; i <= hi; i++) out.push(i);
        return mkSet(out);
      }
      case "@@": {
        const f = this.evaluate(x, ctx);
        const g = this.evaluate(y, ctx);
        if (!(f instanceof TFun) || !(g instanceof TFun)) throw new EvalError("@@ needs functions");
        const dom = [...f.dom];
        const val = [...f.val];
        for (let i = 0; i < g.dom.length; i++) {
          if (!f.map.has(key(g.dom[i] as Value))) {
            dom.push(g.dom[i] as Value);
            val.push(g.val[i] as Value);
          }
        }
        return new TFun(dom, val);
      }
      case ":>":
        return new TFun([this.evaluate(x, ctx)], [this.evaluate(y, ctx)]);
      case "DOMAIN": {
        const f = this.evaluate(x, ctx);
        if (typeof f === "string") return mkSet([...f].map((_, i) => i + 1));
        if (!(f instanceof TFun)) throw new EvalError(`DOMAIN of a ${describe(f)}`);
        return mkSet(f.dom);
      }
      case "SUBSET":
        return new Lazy({ lazy: "subset", of: this.set(x, ctx) });
      case "UNION":
        return mkSet(elements(this.set(x, ctx)).flatMap((s) => elements(s)));
      case "ENABLED":
        return this.enabled(x, ctx);
      case "UNCHANGED":
        return this.unchangedVars(x, ctx).every((i) => {
          const n = ctx.nxt[i];
          if (n === undefined) throw new EvalError(`${this.vars[i]}' is read before it is assigned`);
          return equal(n, ctx.cur[i] as Value);
        });
    }
    throw new EvalError(`operator ${op} is not supported`);
  }

  enabled(a: Expr, ctx: Ctx): boolean {
    const nxt: Array<Value | undefined> = new Array(this.vars.length).fill(undefined);
    return this.enumerate(a, { ...ctx, nxt, primed: false, init: false }, () => true);
  }

  private unchangedVars(e: Expr, ctx: Ctx): number[] {
    if (e.k === "tuple") return e.items.flatMap((x) => this.unchangedVars(x, ctx));
    if (e.k === "id") {
      const vi = this.varIndex.get(e.name);
      if (vi !== undefined && lookupEnv(ctx.env, e.name) === undefined) return [vi];
      const def = this.defs.get(e.name);
      if (def && def.params.length === 0) return this.unchangedVars(def.body, ctx);
    }
    throw new EvalError("UNCHANGED takes variables or a tuple of variables");
  }

  // The variable an `x' = e` or `x' \in S` conjunct can assign, if any.
  private target(lhs: Expr, ctx: Ctx): number | undefined {
    const id = ctx.init ? lhs : lhs.k === "prime" ? lhs.e : undefined;
    if (!id || id.k !== "id" || lookupEnv(ctx.env, id.name) !== undefined) return undefined;
    return this.varIndex.get(id.name);
  }

  private assign(i: number, v: Value, ctx: Ctx, k: (c: Ctx) => boolean): boolean {
    const cur = ctx.nxt[i];
    if (cur !== undefined) return equal(cur, v) ? k(ctx) : false;
    ctx.nxt[i] = v;
    try {
      return k(ctx);
    } finally {
      ctx.nxt[i] = undefined;
    }
  }

  // Calls k once per way the action holds. Returns true when k asks to stop.
  enumerate(e: Expr, ctx: Ctx, k: (c: Ctx) => boolean): boolean {
    switch (e.k) {
      case "and": {
        const go = (i: number, c: Ctx): boolean =>
          i === e.items.length ? k(c) : this.enumerate(e.items[i] as Expr, c, (c2) => go(i + 1, c2));
        return go(0, ctx);
      }
      case "or":
        for (const x of e.items) if (this.enumerate(x, ctx, k)) return true;
        return false;
      case "quant":
        if (e.q === "E") return this.bind(e.bounds, ctx, (c) => this.enumerate(e.body, c, k));
        break;
      case "if":
        return this.bool(e.c, ctx) ? this.enumerate(e.t, ctx, k) : this.enumerate(e.e, ctx, k);
      case "let":
        return this.enumerate(e.body, this.letCtx(e.defs, ctx), k);
      case "id":
      case "call": {
        const target = this.resolveDef(e.name, ctx);
        if (target) {
          const args = e.k === "call" ? e.args.map((a) => this.evaluate(a, ctx)) : [];
          return this.enumerate(target.def.body, this.callDef(target.def, target.env, args, ctx), k);
        }
        break;
      }
      case "op": {
        const [lhs, rhs] = e.args as [Expr, Expr];
        if (e.op === "=" || e.op === "\\in") {
          const i = this.target(lhs, ctx);
          if (i !== undefined) {
            const rv = this.evaluate(rhs, ctx);
            if (e.op === "=") return this.assign(i, rv, ctx, k);
            for (const v of elements(rv)) if (this.assign(i, v, ctx, k)) return true;
            return false;
          }
        }
        if (e.op === "UNCHANGED") {
          const vars = this.unchangedVars(lhs, ctx);
          const go = (j: number, c: Ctx): boolean =>
            j === vars.length ? k(c) : this.assign(vars[j] as number, c.cur[vars[j] as number] as Value, c, (c2) => go(j + 1, c2));
          return go(0, ctx);
        }
        break;
      }
    }
    return this.bool(e, ctx) ? k(ctx) : false;
  }
}

