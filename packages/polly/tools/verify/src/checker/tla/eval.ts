// Evaluator for the parsed subset. The compiler (compile.ts) uses it for
// expressions that read no variable: each is evaluated once and its value
// becomes a literal in the compiled code. Actions are compiled, never
// interpreted, so ENABLED and UNCHANGED are not evaluated here.

import { type Bound, type Def, type Expr, isExpr } from "./parser";
import {
  apply,
  at,
  describe,
  elements,
  equal,
  key,
  Lazy,
  member,
  mkRecord,
  mkSeq,
  mkSet,
  type SetValue,
  seqItems,
  show,
  TFun,
  TlaEvalError,
  TSet,
  type Value,
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

const BUILTIN_OPS = new Set([
  "Len",
  "Append",
  "Head",
  "Tail",
  "SubSeq",
  "Seq",
  "Cardinality",
  "IsFiniteSet",
  "Print",
  "Assert",
  "ToString",
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
      if (!isExpr(e)) return;
      const node = e;
      if (
        node.k === "prime" ||
        (node.k === "op" && (node.op === "ENABLED" || node.op === "UNCHANGED"))
      )
        ok = false;
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
    if (typeof v !== "boolean") throw new TlaEvalError(`expected a boolean, got ${show(v)}`);
    return v;
  }
  private num(e: Expr, ctx: Ctx): number {
    const v = this.evaluate(e, ctx);
    if (typeof v !== "number") throw new TlaEvalError(`expected a number, got ${show(v)}`);
    return v;
  }
  private set(e: Expr, ctx: Ctx): SetValue {
    const v = this.evaluate(e, ctx);
    if (!(v instanceof TSet || v instanceof Lazy))
      throw new TlaEvalError(`expected a set, got ${show(v)}`);
    return v;
  }

  private readVar(i: number, name: string, ctx: Ctx): Value {
    const v = ctx.primed ? ctx.nxt[i] : ctx.cur[i];
    if (v === undefined)
      throw new TlaEvalError(`${name}${ctx.primed ? "'" : ""} is read before it is assigned`);
    return v;
  }

  private callDef(def: Def, env: Env, args: Value[], ctx: Ctx): Ctx {
    if (args.length !== def.params.length)
      throw new TlaEvalError(`${def.name} takes ${def.params.length} arguments`);
    let e = env;
    for (const [i, name] of def.params.entries()) e = { name, b: at(args, i), up: e };
    return { ...ctx, env: e, at: undefined };
  }

  // The definition an identifier or call names, if it is a user definition.
  private resolveDef(
    name: string,
    ctx: Ctx
  ): { def: Def; env: Env; closure?: Closure } | undefined {
    const bound = lookupEnv(ctx.env, name);
    if (bound !== undefined)
      return bound instanceof Closure
        ? { def: bound.def, env: bound.env, closure: bound }
        : undefined;
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
        if (ctx.primed) throw new TlaEvalError("a prime inside a prime");
        return this.evaluate(e.e, { ...ctx, primed: true });
      case "index": {
        const f = this.evaluate(e.f, ctx);
        const args = e.args.map((a) => this.evaluate(a, ctx));
        return apply(f, args.length === 1 ? at(args, 0) : mkSeq(args));
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
        if (e.bounds.length !== 1 || !b || b.vars.length !== 1)
          throw new TlaEvalError("[x \\in S, y \\in T |-> e] is not supported");
        const name = at(b.vars, 0);
        const dom = elements(this.set(b.set, ctx));
        return new TFun(
          dom,
          dom.map((v) => this.evaluate(e.e, { ...ctx, env: { name, b: v, up: ctx.env } }))
        );
      }
      case "rec":
        return mkRecord(e.fields.map(([n, x]) => [n, this.evaluate(x, ctx)]));
      case "recSet":
        return new Lazy({
          lazy: "recSet",
          fields: e.fields.map(([n, x]) => [n, this.set(x, ctx)]),
        });
      case "funSet":
        return new Lazy({
          lazy: "funSet",
          dom: this.set(e.dom, ctx),
          range: this.set(e.range, ctx),
        });
      case "except": {
        let f = this.evaluate(e.f, ctx);
        for (const clause of e.clauses) f = this.update(f, clause.path, 0, clause.value, ctx);
        return f;
      }
      case "at":
        if (ctx.at === undefined) throw new TlaEvalError("@ outside EXCEPT");
        return ctx.at;
      case "if":
        return this.bool(e.c, ctx) ? this.evaluate(e.t, ctx) : this.evaluate(e.e, ctx);
      case "let":
        return this.evaluate(e.body, this.letCtx(e.defs, ctx));
      case "choose": {
        for (const v of elements(this.set(e.set, ctx))) {
          if (this.bool(e.pred, { ...ctx, env: { name: e.v, b: v, up: ctx.env } })) return v;
        }
        throw new TlaEvalError("CHOOSE found no element");
      }
      case "quant": {
        if (e.q === "E") return this.bind(e.bounds, ctx, (c) => this.bool(e.body, c));
        return !this.bind(e.bounds, ctx, (c) => !this.bool(e.body, c));
      }
      case "actBox":
      case "temporal":
        throw new TlaEvalError("a temporal formula in a safety check");
      case "cover":
        throw new TlaEvalError("a coverage counter in an expression the compiler took as constant");
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
      const { name, set } = at(flat, i);
      for (const v of elements(this.set(set, c))) {
        if (go(i + 1, { ...c, env: { name, b: v, up: c.env } })) return true;
      }
      return false;
    };
    return go(0, ctx);
  }

  private update(
    f: Value,
    path: Array<{ index: Expr[] } | { field: string }>,
    i: number,
    value: Expr,
    ctx: Ctx
  ): Value {
    if (i === path.length) return this.evaluate(value, { ...ctx, at: f });
    if (!(f instanceof TFun)) throw new TlaEvalError(`EXCEPT on a ${describe(f)}`);
    const step = at(path, i);
    let k: Value;
    if ("field" in step) k = step.field;
    else {
      const args = step.index.map((a) => this.evaluate(a, ctx));
      k = args.length === 1 ? at(args, 0) : mkSeq(args);
    }
    const j = f.map.get(key(k));
    if (j === undefined) return f; // TLA+: EXCEPT outside the domain leaves f unchanged
    const val = f.val.slice();
    val[j] = this.update(at(f.val, j), path, i + 1, value, ctx);
    return new TFun(f.dom, val);
  }

  private ident(name: string, ctx: Ctx): Value {
    const bound = lookupEnv(ctx.env, name);
    if (bound !== undefined) {
      if (!(bound instanceof Closure)) return bound;
      if (bound.def.params.length > 0) throw new TlaEvalError(`${name} needs arguments`);
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
      if (def.params.length > 0) throw new TlaEvalError(`${name} needs arguments`);
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
    throw new TlaEvalError(`unknown identifier ${name}`);
  }

  private call(name: string, argExprs: Expr[], ctx: Ctx): Value {
    const target = this.resolveDef(name, ctx);
    if (target) {
      const args = argExprs.map((a) => this.evaluate(a, ctx));
      return this.evaluate(target.def.body, this.callDef(target.def, target.env, args, ctx));
    }
    if (!BUILTIN_OPS.has(name)) throw new TlaEvalError(`unknown operator ${name}`);
    const args = argExprs.map((a) => this.evaluate(a, ctx));
    const a = at(args, 0);
    const [, b, c] = args;
    switch (name) {
      case "Len":
        return typeof a === "string" ? a.length : seqItems(a).length;
      case "Append":
        return mkSeq([...seqItems(a), at(args, 1)]);
      case "Head": {
        const items = seqItems(a);
        if (items.length === 0) throw new TlaEvalError("Head of an empty sequence");
        return at(items, 0);
      }
      case "Tail": {
        const items = seqItems(a);
        if (items.length === 0) throw new TlaEvalError("Tail of an empty sequence");
        return mkSeq(items.slice(1));
      }
      case "SubSeq": {
        if (typeof b !== "number" || typeof c !== "number")
          throw new TlaEvalError("SubSeq needs numbers");
        if (typeof a === "string") return a.slice(b - 1, Math.max(b - 1, c));
        const items = seqItems(a);
        if (b > c) return mkSeq([]);
        if (b < 1 || c > items.length)
          throw new TlaEvalError(`SubSeq(${show(a)}, ${b}, ${c}) is out of range`);
        return mkSeq(items.slice(b - 1, c));
      }
      case "Seq":
        if (!(a instanceof TSet || a instanceof Lazy)) throw new TlaEvalError("Seq needs a set");
        return new Lazy({ lazy: "Seq", of: a });
      case "Cardinality":
        return elements(a).length;
      case "IsFiniteSet":
        return a instanceof TSet;
      case "Print":
        return at(args, 1);
      case "Assert":
        if (a !== true) throw new TlaEvalError(`Assert failed: ${show(at(args, 1))}`);
        return true;
      case "ToString":
        return show(a);
      case "TLCGet":
        if (a !== "level") throw new TlaEvalError(`TLCGet(${show(a)}) is not supported`);
        if (ctx.level === undefined)
          throw new TlaEvalError('TLCGet("level") outside a state check');
        return ctx.level;
    }
    throw new TlaEvalError(`unknown operator ${name}`);
  }

  private op(op: string, args: Expr[], ctx: Ctx): Value {
    const x = at(args, 0);
    // Unary operators have no second argument; reading it for one is a defect.
    const second = (): Expr => at(args, 1);
    switch (op) {
      case "=":
        return equal(this.evaluate(x, ctx), this.evaluate(second(), ctx));
      case "#":
        return !equal(this.evaluate(x, ctx), this.evaluate(second(), ctx));
      case "<":
        return this.num(x, ctx) < this.num(second(), ctx);
      case ">":
        return this.num(x, ctx) > this.num(second(), ctx);
      case "<=":
        return this.num(x, ctx) <= this.num(second(), ctx);
      case ">=":
        return this.num(x, ctx) >= this.num(second(), ctx);
      case "+":
        return this.num(x, ctx) + this.num(second(), ctx);
      case "-":
        return this.num(x, ctx) - this.num(second(), ctx);
      case "*":
        return this.num(x, ctx) * this.num(second(), ctx);
      case "%": {
        const a = this.num(x, ctx);
        const b = this.num(second(), ctx);
        return ((a % b) + b) % b;
      }
      case "\\div":
        return Math.floor(this.num(x, ctx) / this.num(second(), ctx));
      case "neg":
        return -this.num(x, ctx);
      case "~":
        return !this.bool(x, ctx);
      case "=>":
        return !this.bool(x, ctx) || this.bool(second(), ctx);
      case "<=>":
        return this.bool(x, ctx) === this.bool(second(), ctx);
      case "\\in":
        return member(this.evaluate(x, ctx), this.evaluate(second(), ctx));
      case "\\notin":
        return !member(this.evaluate(x, ctx), this.evaluate(second(), ctx));
      case "\\subseteq": {
        const b = this.evaluate(second(), ctx);
        return elements(this.set(x, ctx)).every((v) => member(v, b));
      }
      case "\\union":
        return mkSet([...elements(this.set(x, ctx)), ...elements(this.set(second(), ctx))]);
      case "\\intersect": {
        const b = this.set(second(), ctx);
        return mkSet(elements(this.set(x, ctx)).filter((v) => member(v, b)));
      }
      case "\\": {
        const b = this.set(second(), ctx);
        return mkSet(elements(this.set(x, ctx)).filter((v) => !member(v, b)));
      }
      case "..": {
        const lo = this.num(x, ctx);
        const hi = this.num(second(), ctx);
        const out: number[] = [];
        for (let i = lo; i <= hi; i++) out.push(i);
        return mkSet(out);
      }
      case "@@": {
        const f = this.evaluate(x, ctx);
        const g = this.evaluate(second(), ctx);
        if (!(f instanceof TFun) || !(g instanceof TFun))
          throw new TlaEvalError("@@ needs functions");
        const dom = [...f.dom];
        const val = [...f.val];
        for (const [i, d] of g.dom.entries()) {
          if (!f.map.has(key(d))) {
            dom.push(d);
            val.push(at(g.val, i));
          }
        }
        return new TFun(dom, val);
      }
      case ":>":
        return new TFun([this.evaluate(x, ctx)], [this.evaluate(second(), ctx)]);
      case "DOMAIN": {
        const f = this.evaluate(x, ctx);
        if (typeof f === "string") return mkSet([...f].map((_, i) => i + 1));
        if (!(f instanceof TFun)) throw new TlaEvalError(`DOMAIN of a ${describe(f)}`);
        return mkSet(f.dom);
      }
      case "SUBSET":
        return new Lazy({ lazy: "subset", of: this.set(x, ctx) });
      case "UNION":
        return mkSet(elements(this.set(x, ctx)).flatMap((s) => elements(s)));
      case "ENABLED":
      case "UNCHANGED":
        throw new TlaEvalError(`${op} in an expression the compiler took as constant`);
    }
    throw new TlaEvalError(`operator ${op} is not supported`);
  }
}
