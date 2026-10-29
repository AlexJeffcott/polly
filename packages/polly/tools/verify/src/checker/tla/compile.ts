// Compiles the parsed spec to JavaScript over interned value IDs (runtime.ts).
//
// Actions become nested for/if code. Which primed variables are assigned at
// each point is known while compiling, so `x' = e` compiles to either an
// assignment or a comparison, and a step that leaves a variable unassigned is
// found here, not at run time. A subexpression that reads no variable is
// evaluated once, by the interpreter, and its ID becomes a literal.

import { type Ctx, Evaluator } from "./eval";
import { type Def, type ExceptClause, type Expr, isExpr } from "./parser";
import { type LazyRT, Runtime, type SetRT } from "./runtime";
import { at, elements, isFiniteSet, Lazy, mkSet, TlaEvalError, type Value } from "./values";

// A short form of an expression for error messages.
function brief(e: Expr): string {
  const s = JSON.stringify(e);
  return s.length > 160 ? `${s.slice(0, 160)}...` : s;
}

export class CompileError extends Error {}

// What a name in scope stands for.
type Binding =
  | { k: "js"; code: string } // a JS expression for an ID, already evaluated
  | { k: "macro"; def: Def; scope: Scope; args?: Binding[] }; // substituted at each use

type Scope = {
  locals: Map<string, Binding>;
  cur: string[]; // JS name of each unprimed variable
  nxt: Array<string | undefined>; // JS name of each assigned primed variable
  primed: boolean;
  init: boolean;
  at?: string;
  // Generated code for f[x] -> a local that already holds it (loops over
  // DOMAIN f and 1..Len(f) bind it).
  memo?: Map<string, string>;
  // Guards already tested on this path (generated code).
  guards?: Set<string>;
  // Inside ENABLED: `x' = e` binds x' to the code of e, evaluated only if read.
  lazyAssign?: boolean;
};

export type Compiled = {
  rt: Runtime;
  vars: string[];
  source: string;
  init: () => void;
  next: (s: Int32Array) => void;
  constraint: (s: Int32Array) => boolean;
  invariants: Array<{ name: string; holds: (s: Int32Array) => boolean }>;
  setLevel: (l: number) => void;
  // Whether the constraint and the invariants read TLCGet("level").
  constraintReadsLevel: boolean;
  invariantsReadLevel: boolean;
};

const BOOL_OPS = new Set([
  "=",
  "#",
  "<",
  ">",
  "<=",
  ">=",
  "\\in",
  "\\notin",
  "\\subseteq",
  "~",
  "=>",
  "<=>",
  "ENABLED",
  "UNCHANGED",
]);
const NUM_OPS = new Set(["+", "-", "*", "%", "\\div", "neg"]);
const NUM_CALLS = new Set(["Len", "Cardinality", "TLCGet"]);

export function compileSpec(opts: {
  defs: Map<string, Def>;
  constants: Map<string, Value>;
  vars: string[];
  init: Expr;
  next: Expr;
  constraints: Expr[];
  invariants: Array<{ name: string; e: Expr }>;
  emit: () => void;
  nx: Int32Array;
  // Counters for the `cover` nodes in the spec, indexed by slot.
  cov?: Int32Array;
}): Compiled {
  const c = new Compiler(opts.defs, opts.constants, opts.vars);
  return c.build(opts);
}

class Compiler {
  readonly rt = new Runtime();
  private readonly ev: Evaluator;
  private readonly varIndex: Map<string, number>;
  private readonly lazies: LazyRT[] = [];
  private readonly constArrays: string[] = [];
  private readonly lifted: string[] = [];
  private readonly constLevel = new Map<string, boolean>();
  private uid = 0;

  constructor(
    private readonly defs: Map<string, Def>,
    private readonly constants: Map<string, Value>,
    private readonly vars: string[]
  ) {
    this.ev = new Evaluator(defs, constants, vars);
    this.varIndex = new Map(vars.map((v, i) => [v, i]));
  }

  private fresh(p: string): string {
    return `${p}${this.uid++}`;
  }

  /**
   * A function body that must run as an expression, as a call to a function
   * at module level. A closure called at once (`(() => { ... })()`) cost one
   * scope and one function object per call: on webrtc-p2p-chat/client that
   * was 4.8 GiB of uncollected garbage. The free variables are the
   * generated names (`s0`, `x10`, ...) and `S` that the body reads and does
   * not declare; they become parameters. A body that assigns to a variable
   * it does not declare stays a closure, as a parameter would not carry the
   * assignment out.
   */
  private lift(body: string): string {
    const code = body.replace(/"(?:[^"\\]|\\.)*"/g, '""');
    // `const a = ..., b = ...` declares b too; generated code has no other `, x =`.
    const declared = new Set(
      [
        ...code.matchAll(/\b(?:const|let)\s+([A-Za-z]+\d+)\b/g),
        ...code.matchAll(/,\s*([A-Za-z]+\d+)\s*=(?!=)/g),
      ].map((m) => m[1])
    );
    const free = [
      ...new Set(
        [...code.matchAll(/(?<![.\w])([A-Za-z]+\d+|S)\b/g)]
          .map((m) => m[1] ?? "")
          // C, F and P names are module-level: const sets, lifted functions, predicates.
          .filter((x) => x !== "" && !declared.has(x) && !/^[CFP]\d+$/.test(x))
      ),
    ];
    const written = new Set(
      [...code.matchAll(/(?<![.\w])([A-Za-z]+\d+|S)\s*(?:[-+*/]?=(?!=)|\+\+|--)/g)].map((m) => m[1])
    );
    if (free.some((x) => written.has(x))) return `(() => { ${body} })()`;
    const name = this.fresh("F");
    this.lifted.push(`function ${name}(${free.join(", ")}) { ${body} }`);
    return `${name}(${free.join(", ")})`;
  }

  build(o: Parameters<typeof compileSpec>[0]): Compiled {
    const n = this.vars.length;
    const curNames = this.vars.map((_, i) => `s${i}`);
    const readState = curNames.map((s, i) => `const ${s} = S[${i}];`).join(" ");
    const leaf = (sc: Scope) => {
      const parts: string[] = [];
      for (let i = 0; i < n; i++) {
        const name = sc.nxt[i];
        // TLC reports this when the step runs; a branch that never runs is no error.
        if (!name)
          return `throw new Error(${JSON.stringify(`the step leaves ${this.vars[i]} unassigned`)});`;
        parts.push(`NX[${i}] = ${name};`);
      }
      return `${parts.join(" ")} emit();`;
    };
    const empty = (cur: string[], init: boolean): Scope => ({
      locals: new Map(),
      cur,
      nxt: new Array(n).fill(undefined),
      primed: false,
      init,
    });

    // In Init the unprimed variables are the ones being assigned.
    const initScope = empty(new Array(n).fill(undefined), true);
    const initCode = this.act(o.init, initScope, leaf);
    const nextCode = this.act(this.hoist(o.next), empty(curNames, false), leaf);
    // A state predicate is split into its top-level conjuncts. Each conjunct
    // is a pure function of the state variables (and LEVEL) its code reads,
    // so with one or two of them its result is cached by their value IDs.
    const memoDefs: string[] = [];
    const conjuncts = (e: Expr): Expr[] => {
      if (e.k === "and") return e.items.flatMap(conjuncts);
      const def = e.k === "id" ? this.defs.get(e.name) : undefined;
      if (def && def.params.length === 0 && !this.varIndex.has(def.name)) {
        return conjuncts(def.body);
      }
      return [e];
    };
    const stateFn = (e: Expr) => {
      const parts = conjuncts(e).map((c) => {
        const code = this.bo(c, empty(curNames, false));
        const deps: string[] = [
          ...new Set([...code.matchAll(/\bs(\d+)\b/g)].map((m) => `S[${m[1]}]`)),
        ];
        if (/\bLEVEL\b/.test(code)) deps.push("LEVEL");
        const fn = `(S) => { ${readState} return ${code}; }`;
        const name = this.fresh("P");
        if (deps.length === 1) memoDefs.push(`const ${name} = memo1((S) => ${deps[0]}, ${fn});`);
        else if (deps.length === 2)
          memoDefs.push(`const ${name} = memo2((S) => ${deps[0]}, (S) => ${deps[1]}, ${fn});`);
        else memoDefs.push(`const ${name} = ${fn};`);
        return `${name}(S)`;
      });
      return `function (S) { return ${parts.length ? parts.join(" && ") : "true"}; }`;
    };
    const constraintCode =
      o.constraints.length === 0
        ? "function () { return true; }"
        : stateFn({ k: "and", items: o.constraints });
    const invCodes = o.invariants.map((inv) => stateFn(inv.e));

    const source = [
      `"use strict";`,
      `let LEVEL = 1;`,
      // Cache of a predicate by one value ID: 0 unknown, 1 true, 2 false.
      `function memo1(key, fn) { let c = new Uint8Array(1 << 16); return (S) => { const k = key(S); if (k >= c.length) { const d = new Uint8Array(Math.max(k + 1, c.length * 2)); d.set(c); c = d; } const r = c[k]; if (r !== 0) return r === 1; const v = fn(S); c[k] = v ? 1 : 2; return v; }; }`,
      // Cache by two value IDs: open addressing over (a, b) pairs; 0 = empty slot.
      `function memo2(k1, k2, fn) {
        let cap = 1 << 16, keys = new Int32Array(cap * 2), res = new Uint8Array(cap), size = 0;
        const slot = (a, b) => { let h = Math.imul(a, 0x9e3779b1) ^ Math.imul(b + 0x7f4a7c15, 0x85ebca6b); h ^= h >>> 15; let i = h & (cap - 1); while (res[i] !== 0 && (keys[2 * i] !== a || keys[2 * i + 1] !== b)) i = (i + 1) & (cap - 1); return i; };
        const grow = () => { const ok = keys, or = res, oc = cap; cap *= 2; keys = new Int32Array(cap * 2); res = new Uint8Array(cap); for (let j = 0; j < oc; j++) if (or[j] !== 0) { const i = slot(ok[2 * j], ok[2 * j + 1]); keys[2 * i] = ok[2 * j]; keys[2 * i + 1] = ok[2 * j + 1]; res[i] = or[j]; } };
        return (S) => { const a = k1(S), b = k2(S); const i = slot(a, b); const r = res[i]; if (r !== 0) return r === 1; const v = fn(S); keys[2 * i] = a; keys[2 * i + 1] = b; res[i] = v ? 1 : 2; if (++size * 2 > cap) grow(); return v; };
      }`,
      ...this.constArrays,
      ...this.lifted,
      `const init = function () { ${initCode} };`,
      `const next = function (S) { ${readState} ${nextCode} };`,
      ...memoDefs,
      `const constraint = ${constraintCode};`,
      `const invariants = [${invCodes.join(",\n")}];`,
      `return { init, next, constraint, invariants, setLevel: (l) => { LEVEL = l; } };`,
    ].join("\n");

    let made: {
      init: () => void;
      next: (s: Int32Array) => void;
      constraint: (s: Int32Array) => boolean;
      invariants: Array<(s: Int32Array) => boolean>;
      setLevel: (l: number) => void;
    };
    try {
      made = new Function("R", "NX", "emit", "LZ", "COV", source)(
        this.rt,
        o.nx,
        o.emit,
        this.lazies,
        o.cov ?? new Int32Array(0)
      );
    } catch (err) {
      throw new CompileError(
        `generated code does not compile: ${err instanceof Error ? err.message : String(err)}`
      );
    }
    return {
      rt: this.rt,
      vars: this.vars,
      source,
      init: made.init,
      next: made.next,
      constraint: made.constraint,
      invariants: o.invariants.map((inv, i) => ({
        name: inv.name,
        holds: at(made.invariants, i),
      })),
      setLevel: made.setLevel,
      constraintReadsLevel: constraintCode.includes("LEVEL"),
      invariantsReadLevel: invCodes.some((c) => c.includes("LEVEL")),
    };
  }

  // ------------------------------------------------------------ guard hoisting
  // \E x \in S : (G /\ B)  ->  G /\ \E x \in S : B, when G is a pure state
  // guard that does not name x. Both give the same successors, the same
  // number of times: with S empty both give none, and a pure guard does not
  // depend on where it sits in a conjunction. A called definition is
  // substituted first, so its guards can move out of the quantifiers.
  private hoist(e: Expr, depth = 0): Expr {
    switch (e.k) {
      case "id":
      case "call": {
        const sub = depth < 8 ? this.substituteCall(e) : undefined;
        return sub ? this.hoist(sub, depth + 1) : e;
      }
      case "if":
        return { ...e, t: this.hoist(e.t, depth), e: this.hoist(e.e, depth) };
      case "let":
        return { ...e, body: this.hoist(e.body, depth) };
      case "and":
        return { k: "and", items: e.items.map((x) => this.hoist(x, depth)) };
      case "or":
        return { k: "or", items: e.items.map((x) => this.hoist(x, depth)) };
      case "quant": {
        if (e.q !== "E") return e;
        const bound = new Set(e.bounds.flatMap((b) => b.vars));
        // Calls among the conjuncts are substituted and their conjuncts spliced in.
        const flatten = (x: Expr, depth: number): Expr[] => {
          if (x.k === "and") return x.items.flatMap((y) => flatten(y, depth));
          const sub = depth < 4 ? this.substituteCall(x) : undefined;
          return sub ? flatten(sub, depth + 1) : [x];
        };
        const flat = flatten(e.body, 0);
        const body = this.hoist(flat.length === 1 ? at(flat, 0) : { k: "and", items: flat }, depth);
        const items = body.k === "and" ? body.items : [body];
        const out: Expr[] = [];
        const keep: Expr[] = [];
        for (const it of items) {
          const names = this.freeNames(it);
          if (keep.length === 0 && this.isPureGuard(it) && ![...bound].some((v) => names.has(v)))
            out.push(it);
          else keep.push(it);
        }
        if (out.length === 0) return { ...e, body };
        const inner: Expr =
          keep.length === 0
            ? { k: "bool", v: true }
            : keep.length === 1
              ? at(keep, 0)
              : { k: "and", items: keep };
        return { k: "and", items: [...out, { ...e, body: inner }] };
      }
    }
    return e;
  }

  // The body of a call to a top-level definition with its arguments put in,
  // or undefined when a bound name in the body could capture an argument.
  private substituteCall(e: Expr): Expr | undefined {
    if (e.k !== "call" && e.k !== "id") return undefined;
    const def = this.defs.get(e.name);
    if (!def || this.varIndex.has(e.name) || this.constants.has(e.name)) return undefined;
    const args = e.k === "call" ? e.args : [];
    if (args.length !== def.params.length) return undefined;
    const argNames = new Set(args.flatMap((a) => [...this.freeNames(a)]));
    const binders = this.binders(def.body);
    if ([...argNames].some((n) => binders.has(n))) return undefined;
    const map = new Map(def.params.map((p, i) => [p, at(args, i)]));
    const sub = (x: unknown): unknown => {
      if (x === null || typeof x !== "object") return x;
      if (Array.isArray(x)) return x.map(sub);
      if (isExpr(x) && x.k === "id") {
        const arg = map.get(x.name);
        if (arg) return arg;
      }
      const out: Record<string, unknown> = {};
      for (const [k, v] of Object.entries(x)) out[k] = sub(v);
      return out;
    };
    const body = sub(def.body);
    if (typeof body !== "object" || body === null || !isExpr(body))
      throw new CompileError(`substituting into ${def.name} lost its shape`);
    return body;
  }

  // Names a body binds: quantifier, set, CHOOSE, function and LET names.
  private binders(e: Expr): Set<string> {
    const out = new Set<string>();
    const walk = (x: unknown): void => {
      if (x === null || typeof x !== "object") return;
      if (isExpr(x)) {
        if ("bounds" in x) for (const b of x.bounds) for (const v of b.vars) out.add(v);
        if (x.k === "setFilter" || x.k === "choose") out.add(x.v);
        if (x.k === "let")
          for (const d of x.defs) {
            out.add(d.name);
            for (const p of d.params) out.add(p);
          }
      }
      for (const v of Object.values(x)) walk(v);
    };
    walk(e);
    return out;
  }

  // No prime, UNCHANGED, ENABLED or @, and no call to a definition with one.
  private isPureGuard(e: Expr, seen = new Set<string>()): boolean {
    let ok = true;
    const walk = (x: unknown): void => {
      if (!ok || x === null || typeof x !== "object") return;
      if (isExpr(x)) {
        // A cover marker counts where it stands, so it never moves.
        if (
          x.k === "prime" ||
          x.k === "at" ||
          x.k === "actBox" ||
          x.k === "temporal" ||
          x.k === "cover"
        )
          ok = false;
        else if (x.k === "op" && (x.op === "UNCHANGED" || x.op === "ENABLED")) ok = false;
        else if (x.k === "id" || x.k === "call") {
          const def = this.defs.get(x.name);
          if (def && !seen.has(x.name)) {
            seen.add(x.name);
            if (!this.isPureGuard(def.body, seen)) ok = false;
          }
        }
      }
      for (const v of Object.values(x)) walk(v);
    };
    walk(e);
    return ok;
  }

  // ------------------------------------------------------------ constants
  private defIsConst(name: string, seen: Set<string>): boolean {
    const cached = this.constLevel.get(name);
    if (cached !== undefined) return cached;
    if (seen.has(name)) return false;
    seen.add(name);
    const def = this.defs.get(name);
    if (!def) return true;
    const inner = new Set(def.params);
    const ok = this.exprIsConst(def.body, inner, seen);
    this.constLevel.set(name, ok);
    return ok;
  }

  // True when e reads no variable, no bound name outside `bound`, no prime,
  // no @ and no TLCGet: its value is the same in every state.
  private exprIsConst(e: Expr, bound: Set<string>, seen = new Set<string>()): boolean {
    switch (e.k) {
      case "num":
      case "str":
      case "bool":
        return true;
      case "at":
      case "prime":
      case "actBox":
      case "temporal":
      case "cover":
        return false;
      case "id":
      case "call": {
        if (e.k === "call" && e.name === "TLCGet") return false;
        if (e.k === "call" && !e.args.every((a) => this.exprIsConst(a, bound, seen))) return false;
        if (bound.has(e.name)) return true;
        if (this.varIndex.has(e.name)) return false;
        if (this.constants.has(e.name)) return true;
        if (this.defs.has(e.name)) return this.defIsConst(e.name, seen);
        return true; // builtin
      }
      case "op":
        if (e.op === "ENABLED" || e.op === "UNCHANGED") return false;
        return e.args.every((a) => this.exprIsConst(a, bound, seen));
      case "and":
      case "or":
      case "setEnum":
      case "tuple":
        return e.items.every((a) => this.exprIsConst(a, bound, seen));
      case "index":
        return (
          this.exprIsConst(e.f, bound, seen) &&
          e.args.every((a) => this.exprIsConst(a, bound, seen))
        );
      case "dot":
        return this.exprIsConst(e.r, bound, seen);
      case "setFilter":
        return (
          this.exprIsConst(e.set, bound, seen) &&
          this.exprIsConst(e.pred, new Set([...bound, e.v]), seen)
        );
      case "choose":
        return (
          this.exprIsConst(e.set, bound, seen) &&
          this.exprIsConst(e.pred, new Set([...bound, e.v]), seen)
        );
      case "setMap":
      case "fun":
      case "quant": {
        const b = new Set(bound);
        for (const x of e.bounds) {
          if (!this.exprIsConst(x.set, b, seen)) return false;
          for (const v of x.vars) b.add(v);
        }
        return this.exprIsConst(e.k === "quant" ? e.body : e.e, b, seen);
      }
      case "rec":
      case "recSet":
        return e.fields.every(([, x]) => this.exprIsConst(x, bound, seen));
      case "funSet":
        return this.exprIsConst(e.dom, bound, seen) && this.exprIsConst(e.range, bound, seen);
      case "except":
        return (
          this.exprIsConst(e.f, bound, seen) &&
          e.clauses.every(
            (c) =>
              c.path.every(
                (p) => "field" in p || p.index.every((x) => this.exprIsConst(x, bound, seen))
              ) &&
              !this.usesAt(c.value) &&
              this.exprIsConst(c.value, bound, seen)
          )
        );
      case "if":
        return (
          this.exprIsConst(e.c, bound, seen) &&
          this.exprIsConst(e.t, bound, seen) &&
          this.exprIsConst(e.e, bound, seen)
        );
      case "let": {
        const b = new Set(bound);
        for (const d of e.defs) {
          if (!this.exprIsConst(d.body, new Set([...b, ...d.params]), seen)) return false;
          b.add(d.name);
        }
        return this.exprIsConst(e.body, b, seen);
      }
    }
  }

  private usesAt(e: Expr): boolean {
    return JSON.stringify(e).includes('"k":"at"');
  }

  // A constant expression in scope sc: only names bound to constants may be
  // free, and the scope here binds none, so the check uses an empty bound set.
  private isConst(e: Expr, sc: Scope): boolean {
    if (sc.locals.size > 0) {
      // Locals are run-time values; a constant may not read them.
      const free = this.freeNames(e);
      for (const name of free) if (sc.locals.has(name)) return false;
    }
    return this.exprIsConst(e, new Set());
  }

  private freeNames(e: Expr): Set<string> {
    const out = new Set<string>();
    const walk = (x: unknown): void => {
      if (x === null || typeof x !== "object") return;
      if (isExpr(x) && (x.k === "id" || x.k === "call")) out.add(x.name);
      for (const v of Object.values(x)) walk(v);
    };
    walk(e);
    return out;
  }

  // Evaluates a constant expression once; an ID becomes a literal.
  private constant(e: Expr): SetRT {
    const ctx: Ctx = { cur: [], nxt: [], primed: false, init: false, env: null };
    return this.rt.fromValue(this.ev.evaluate(e, ctx));
  }
  // A constant set for a loop: a finite lazy set is listed first.
  private constElems(e: Expr): number {
    const ctx: Ctx = { cur: [], nxt: [], primed: false, init: false, env: null };
    let v = this.ev.evaluate(e, ctx);
    if (v instanceof Lazy) {
      if (!isFiniteSet(v))
        throw new CompileError(`cannot enumerate the infinite set ${v.s.lazy}: ${brief(e)}`);
      v = mkSet(elements(v));
    }
    return this.rt.idOf(v);
  }
  private constCode(e: Expr): { id: string } | { lazy: string } {
    const v = this.constant(e);
    if (typeof v === "number") return { id: `${v}` };
    this.lazies.push(v);
    return { lazy: `LZ[${this.lazies.length - 1}]` };
  }

  // ------------------------------------------------------------ names
  private lookup(name: string, sc: Scope): Binding | undefined {
    return sc.locals.get(name);
  }

  private stateVar(name: string, sc: Scope): string | undefined {
    const i = this.varIndex.get(name);
    if (i === undefined) return undefined;
    if (sc.primed || sc.init) {
      const nm = sc.nxt[i];
      if (!nm)
        throw new CompileError(`${name}${sc.primed ? "'" : ""} is read before it is assigned`);
      return nm;
    }
    return sc.cur[i];
  }

  // Binds a macro's parameters, or a definition's, to argument bindings.
  private enter(def: Def, scope: Scope, args: Binding[], sc: Scope): Scope {
    if (args.length !== def.params.length)
      throw new CompileError(`${def.name} takes ${def.params.length} arguments`);
    const locals = new Map(scope.locals);
    for (const [i, p] of def.params.entries()) locals.set(p, at(args, i));
    return { ...sc, locals, at: undefined };
  }

  // The user definition (or macro) a name or call refers to.
  private target(name: string, sc: Scope): { def: Def; scope: Scope } | undefined {
    const b = this.lookup(name, sc);
    if (b) return b.k === "macro" ? { def: b.def, scope: b.scope } : undefined;
    if (this.varIndex.has(name) || this.constants.has(name)) return undefined;
    const def = this.defs.get(name);
    return def ? { def, scope: { ...sc, locals: new Map() } } : undefined;
  }

  // Arguments as substitution bindings (expression context).
  private argBindings(args: Expr[], sc: Scope): Binding[] {
    return args.map((a): Binding => ({ k: "js", code: `(${this.ex(a, sc)})` }));
  }

  // A macro use: its body compiled in its own scope, primed flag of the use.
  private macroScope(t: { def: Def; scope: Scope }, args: Binding[], sc: Scope): Scope {
    const base: Scope = { ...t.scope, cur: sc.cur, nxt: sc.nxt, primed: sc.primed, init: sc.init };
    return this.enter(t.def, base, args, sc);
  }

  // ------------------------------------------------------------ expressions (ID)
  ex(e: Expr, sc: Scope): string {
    if (this.isConst(e, sc)) {
      const c = this.constCode(e);
      if (!("id" in c))
        throw new CompileError(`an infinite set where a value is needed: ${brief(e)}`);
      return c.id;
    }
    if (this.isBool(e, sc)) return `(${this.bo(e, sc)} ? ${this.rt.TRUE} : ${this.rt.FALSE})`;
    if (this.isNum(e)) return `R.int(${this.nu(e, sc)})`;
    const R = "R";
    switch (e.k) {
      case "id": {
        const b = this.lookup(e.name, sc);
        if (b?.k === "js") return b.code;
        if (b?.k === "macro")
          return this.ex(
            b.def.body,
            this.macroScope({ def: b.def, scope: b.scope }, b.args ?? [], sc)
          );
        const sv = this.stateVar(e.name, sc);
        if (sv) return sv;
        const t = this.target(e.name, sc);
        if (t) return this.ex(t.def.body, this.macroScope(t, [], sc));
        throw new CompileError(`unknown identifier ${e.name}`);
      }
      case "call": {
        const t = this.target(e.name, sc);
        if (t) return this.ex(t.def.body, this.macroScope(t, this.argBindings(e.args, sc), sc));
        const a = e.args.map((x) => this.ex(x, sc));
        switch (e.name) {
          case "Append":
            return `${R}.append(${a[0]}, ${a[1]})`;
          case "SubSeq":
            return `${R}.subSeq(${a[0]}, ${R}.iv(${a[1]}), ${R}.iv(${a[2]}))`;
          case "Head":
            return `${R}.head(${a[0]})`;
          case "Tail":
            return `${R}.tail(${a[0]})`;
        }
        throw new CompileError(`operator ${e.name} is not supported by the compiled engine`);
      }
      case "op": {
        const x = at(e.args, 0);
        const y = (): Expr => at(e.args, 1);
        switch (e.op) {
          case "\\union":
            return `${R}.union(${this.ex(x, sc)}, ${this.ex(y(), sc)})`;
          case "\\":
            return `${R}.filterBy(${this.ex(x, sc)}, ${this.setRef(y(), sc)}, false)`;
          case "\\intersect":
            return `${R}.filterBy(${this.ex(x, sc)}, ${this.setRef(y(), sc)}, true)`;
          case "..":
            return `${R}.range(${this.nu(x, sc)}, ${this.nu(y(), sc)})`;
          case "@@":
            return `${R}.merge(${this.ex(x, sc)}, ${this.ex(y(), sc)})`;
          case ":>":
            return `${R}.funOf([${this.ex(x, sc)}], [${this.ex(y(), sc)}])`;
          case "DOMAIN":
            return `${R}.domain(${this.ex(x, sc)})`;
        }
        throw new CompileError(`operator ${e.op} is not supported by the compiled engine`);
      }
      case "prime":
        if (sc.primed) throw new CompileError("a prime inside a prime");
        return this.ex(e.e, { ...sc, primed: true });
      case "index": {
        if (e.args.length !== 1) throw new CompileError("f[a, b] is not supported");
        const code = `${R}.apply(${this.ex(e.f, sc)}, ${this.ex(at(e.args, 0), sc)})`;
        return sc.memo?.get(code) ?? code;
      }
      case "dot":
        return `${R}.apply(${this.ex(e.r, sc)}, ${this.rt.str(e.field)})`;
      case "setEnum":
        return `${R}.setOf([${e.items.map((x) => this.ex(x, sc)).join(", ")}])`;
      case "tuple":
        return `${R}.seq([${e.items.map((x) => this.ex(x, sc)).join(", ")}])`;
      case "rec": {
        const fields = e.fields.map(([name, x]) => ({
          id: this.rt.str(name),
          code: this.ex(x, sc),
        }));
        fields.sort((p, q) => p.id - q.id);
        return `${R}.rec([${fields.map((f) => f.id).join(", ")}], [${fields.map((f) => f.code).join(", ")}])`;
      }
      case "setFilter": {
        const v = this.fresh("x");
        const body = (s2: Scope) =>
          `if (${this.bo(e.pred, this.bind(s2, e.v, v))}) out.push(${v});`;
        return this.lift(
          `const out = []; ${this.iter(e.set, sc, v, body)} return ${R}.setOf(out);`
        );
      }
      case "setMap": {
        const body = (s2: Scope) => `out.push(${this.ex(e.e, s2)});`;
        return this.lift(
          `const out = []; ${this.iterBounds(e.bounds, sc, body)} return ${R}.setOf(out);`
        );
      }
      case "fun": {
        const [b] = e.bounds;
        if (e.bounds.length !== 1 || !b || b.vars.length !== 1)
          throw new CompileError("[x \\in S, y \\in T |-> e] is not supported");
        const name = at(b.vars, 0);
        // [x \in DOMAIN f \ T |-> f[x]] removes the keys in T from f.
        const set = b.set;
        if (set.k === "op" && set.op === "\\") {
          const d = at(set.args, 0);
          const t = at(set.args, 1);
          if (d.k === "op" && d.op === "DOMAIN" && e.e.k === "index" && e.e.args.length === 1) {
            const arg = at(e.e.args, 0);
            const same =
              JSON.stringify(e.e.f) === JSON.stringify(d.args[0]) &&
              arg.k === "id" &&
              arg.name === name;
            if (same && !this.freeNames(e.e.f).has(name))
              return `${R}.restrict(${this.ex(at(d.args, 0), sc)}, ${this.setRef(t, sc)})`;
          }
        }
        const v = this.fresh("x");
        const inner = this.bind(sc, name, v);
        return `${R}.funOver(${this.ex(b.set, sc)}, (${v}) => ${this.ex(e.e, inner)})`;
      }
      case "except":
        return this.exceptCode(this.ex(e.f, sc), e.clauses, 0, sc);
      case "at":
        if (!sc.at) throw new CompileError("@ outside EXCEPT");
        return sc.at;
      case "if":
        return `(${this.bo(e.c, sc)} ? ${this.ex(e.t, sc)} : ${this.ex(e.e, sc)})`;
      case "let":
        return this.ex(e.body, this.letMacros(e.defs, sc));
      case "choose": {
        const v = this.fresh("x");
        const body = (s2: Scope) => `if (${this.bo(e.pred, this.bind(s2, e.v, v))}) return ${v};`;
        return this.lift(
          `${this.iter(e.set, sc, v, body)} throw new Error("CHOOSE found no element");`
        );
      }
    }
    throw new CompileError(`${e.k} is not supported by the compiled engine`);
  }

  // [f EXCEPT !p.. = v, ...]. Adjacent clauses with the same key code share
  // one lookup and one put at each level; a clause `= @` changes nothing.
  // Clauses run in order, as TLA+ applies them one after another.
  private exceptCode(f: string, clauses: ExceptClause[], i: number, sc: Scope): string {
    const live = clauses.filter(
      (c) =>
        !(c.path.length === i + 0 && c.value.k === "at") &&
        !(c.value.k === "at" && c.path.length >= i)
    );
    if (live.length === 0) return f;
    const v = this.fresh("v");
    const parts: string[] = [];
    let g = 0;
    while (g < live.length) {
      const c = at(live, g);
      if (c.path.length === i) {
        parts.push(`${v} = ${this.ex(c.value, { ...sc, at: v })};`);
        g++;
        continue;
      }
      const keyCode = this.stepKey(at(c.path, i), sc);
      const group: ExceptClause[] = [];
      while (g < live.length) {
        const d = at(live, g);
        if (d.path.length === i || this.stepKey(at(d.path, i), sc) !== keyCode) break;
        group.push(d);
        g++;
      }
      const k = this.fresh("k");
      const idx = this.fresh("j");
      parts.push(
        `{ const ${k} = ${keyCode}; const ${idx} = R.findIdx(${v}, ${k}); if (${idx} >= 0) { ${v} = R.putIdx(${v}, ${idx}, ${this.exceptCode(`R.pool[${idx} + 1]`, group, i + 1, sc)}); } }`
      );
    }
    return this.lift(`let ${v} = ${f}; ${parts.join(" ")} return ${v};`);
  }

  private stepKey(step: { index: Expr[] } | { field: string }, sc: Scope): string {
    if ("field" in step) return `${this.rt.str(step.field)}`;
    if (step.index.length !== 1) throw new CompileError("EXCEPT ![a, b] is not supported");
    return this.ex(at(step.index, 0), sc);
  }

  private bind(sc: Scope, name: string, js: string): Scope {
    const locals = new Map(sc.locals);
    locals.set(name, { k: "js", code: js });
    return { ...sc, locals };
  }
  private letMacros(defs: Def[], sc: Scope): Scope {
    let scope = sc;
    for (const d of defs) {
      const locals = new Map(scope.locals);
      locals.set(d.name, { k: "macro", def: d, scope });
      scope = { ...scope, locals };
    }
    return scope;
  }

  // A set operand as an ID or a lazy set (for membership tests).
  private setRef(e: Expr, sc: Scope): string {
    if (this.isConst(e, sc)) {
      const c = this.constCode(e);
      return "id" in c ? c.id : c.lazy;
    }
    return this.ex(e, sc);
  }

  // ------------------------------------------------------------ numbers
  private isNum(e: Expr): boolean {
    if (e.k === "num") return true;
    if (e.k === "op") return NUM_OPS.has(e.op);
    if (e.k === "call") return NUM_CALLS.has(e.name);
    return false;
  }
  nu(e: Expr, sc: Scope): string {
    if (this.isConst(e, sc)) {
      const v = this.constant(e);
      if (typeof v !== "number") throw new CompileError("a set where a number is needed");
      return `${this.rt.iv(v)}`;
    }
    if (e.k === "op" && NUM_OPS.has(e.op)) {
      const x = at(e.args, 0);
      const y = (): Expr => at(e.args, 1);
      switch (e.op) {
        case "+":
          return `(${this.nu(x, sc)} + ${this.nu(y(), sc)})`;
        case "-":
          return `(${this.nu(x, sc)} - ${this.nu(y(), sc)})`;
        case "*":
          return `(${this.nu(x, sc)} * ${this.nu(y(), sc)})`;
        case "neg":
          return `(-${this.nu(x, sc)})`;
        case "%":
          return `(((${this.nu(x, sc)} % ${this.nu(y(), sc)}) + ${this.nu(y(), sc)}) % ${this.nu(y(), sc)})`;
        case "\\div":
          return `Math.floor(${this.nu(x, sc)} / ${this.nu(y(), sc)})`;
      }
    }
    if (e.k === "call" && !this.target(e.name, sc)) {
      switch (e.name) {
        case "Len":
          return `R.len(${this.ex(at(e.args, 0), sc)})`;
        case "TLCGet": {
          const a = e.args[0];
          if (a?.k !== "str" || a.v !== "level")
            throw new CompileError('TLCGet supports "level" only');
          return "LEVEL";
        }
        case "Cardinality": {
          const s = at(e.args, 0);
          // Cardinality({x \in S : P}) counts without building the set.
          if (s.k === "setFilter") {
            const v = this.fresh("x");
            const body = (s2: Scope) => `if (${this.bo(s.pred, this.bind(s2, s.v, v))}) c++;`;
            return this.lift(`let c = 0; ${this.iter(s.set, sc, v, body)} return c;`);
          }
          return `R.setLen(${this.ex(s, sc)})`;
        }
      }
    }
    return `R.iv(${this.ex(e, sc)})`;
  }

  // ------------------------------------------------------------ booleans
  private isBool(e: Expr, sc: Scope): boolean {
    switch (e.k) {
      case "bool":
      case "and":
      case "or":
      case "quant":
        return true;
      case "op":
        return BOOL_OPS.has(e.op);
      case "call":
        return !this.target(e.name, sc) && e.name === "IsFiniteSet";
    }
    return false;
  }

  bo(e: Expr, sc: Scope): string {
    if (this.isConst(e, sc)) {
      const v = this.constant(e);
      if (v !== this.rt.TRUE && v !== this.rt.FALSE) throw new CompileError("expected a boolean");
      return v === this.rt.TRUE ? "true" : "false";
    }
    switch (e.k) {
      case "and":
        return `(${e.items.map((x) => this.bo(x, sc)).join(" && ")})`;
      case "or":
        return `(${e.items.map((x) => this.bo(x, sc)).join(" || ")})`;
      case "if":
        return `(${this.bo(e.c, sc)} ? ${this.bo(e.t, sc)} : ${this.bo(e.e, sc)})`;
      case "let":
        return this.bo(e.body, this.letMacros(e.defs, sc));
      case "prime":
        if (sc.primed) throw new CompileError("a prime inside a prime");
        return this.bo(e.e, { ...sc, primed: true });
      case "id": {
        const b = this.lookup(e.name, sc);
        if (b?.k === "macro")
          return this.bo(
            b.def.body,
            this.macroScope({ def: b.def, scope: b.scope }, b.args ?? [], sc)
          );
        if (!b && !this.varIndex.has(e.name)) {
          const t = this.target(e.name, sc);
          if (t) return this.bo(t.def.body, this.macroScope(t, [], sc));
        }
        break;
      }
      case "call": {
        const t = this.target(e.name, sc);
        if (t) return this.bo(t.def.body, this.macroScope(t, this.argBindings(e.args, sc), sc));
        break;
      }
      case "quant": {
        if (e.q === "E") {
          return this.lift(
            `${this.iterBounds(e.bounds, sc, (s2) => `if (${this.bo(e.body, s2)}) return true;`)} return false;`
          );
        }
        return this.lift(
          `${this.iterBounds(e.bounds, sc, (s2) => `if (!${this.bo(e.body, s2)}) return false;`)} return true;`
        );
      }
      case "op": {
        const x = at(e.args, 0);
        const y = (): Expr => at(e.args, 1);
        switch (e.op) {
          case "=":
            return `(${this.ex(x, sc)} === ${this.ex(y(), sc)})`;
          case "#":
            return `(${this.ex(x, sc)} !== ${this.ex(y(), sc)})`;
          case "<":
          case ">":
          case "<=":
          case ">=":
            return `(${this.nu(x, sc)} ${e.op} ${this.nu(y(), sc)})`;
          case "~":
            return `(!${this.bo(x, sc)})`;
          case "=>":
            return `(!${this.bo(x, sc)} || ${this.bo(y(), sc)})`;
          case "<=>":
            return `(${this.bo(x, sc)} === ${this.bo(y(), sc)})`;
          case "\\in":
            return this.memberCode(this.ex(x, sc), y(), sc);
          case "\\notin":
            return `(!${this.memberCode(this.ex(x, sc), y(), sc)})`;
          case "\\subseteq":
            return `R.subseteq(${this.ex(x, sc)}, ${this.setRef(y(), sc)})`;
          case "ENABLED": {
            const n = this.vars.length;
            const fresh: Scope = {
              ...sc,
              nxt: new Array(n).fill(undefined),
              primed: false,
              init: false,
              lazyAssign: true,
              guards: undefined,
            };
            return this.lift(`${this.act(x, fresh, () => "return true;")} return false;`);
          }
          case "UNCHANGED":
            return `(${this.unchangedVars(x, sc)
              .map((i) => {
                const nm = sc.nxt[i];
                if (!nm) throw new CompileError(`${this.vars[i]}' is read before it is assigned`);
                return `${nm} === ${sc.cur[i]}`;
              })
              .join(" && ")})`;
        }
        break;
      }
      case "bool":
        return `${e.v}`;
      case "cover":
        return `(COV[${e.slot}]++, true)`;
    }
    return `(${this.ex(e, sc)} === ${this.rt.TRUE})`;
  }

  // x \in S, with the forms that need no set built.
  private memberCode(x: string, s: Expr, sc: Scope): string {
    if (!this.isConst(s, sc)) {
      if (s.k === "op" && s.op === "..") {
        const lo = at(s.args, 0);
        const hi = at(s.args, 1);
        return `R.inRange(${x}, ${this.nu(lo, sc)}, ${this.nu(hi, sc)})`;
      }
      if (s.k === "op" && s.op === "DOMAIN")
        return `R.inDomain(${this.ex(at(s.args, 0), sc)}, ${x})`;
    }
    return `R.member(${x}, ${this.setRef(s, sc)})`;
  }

  // ------------------------------------------------------------ loops
  // Code that runs body once for each element of S, bound to the JS name v.
  // body gets the scope to compile in: loops over DOMAIN f and 1..Len(f) add
  // f[v] to the memo, so the body reads it from a local.
  private iter(s: Expr, sc: Scope, v: string, body: (sc: Scope) => string): string {
    if (this.isConst(s, sc)) {
      const id = this.constElems(s);
      const arr = this.fresh("C");
      this.constArrays.push(`const ${arr} = Int32Array.from(R.elems(${id}));`);
      const i = this.fresh("i");
      return `for (let ${i} = 0; ${i} < ${arr}.length; ${i}++) { const ${v} = ${arr}[${i}]; ${body(sc)} }`;
    }
    const withMemo = (fcode: string, elem: string): Scope => {
      const memo = new Map(sc.memo);
      memo.set(`R.apply(${fcode}, ${v})`, elem);
      return { ...sc, memo };
    };
    if (s.k === "op" && s.op === "..") {
      const lo = at(s.args, 0);
      const hi = at(s.args, 1);
      const i = this.fresh("i");
      const h = this.fresh("h");
      // 1..Len(f): f[v] is bound only if the body reads it.
      const lenOf =
        lo.k === "num" &&
        lo.v === 1 &&
        hi.k === "call" &&
        hi.name === "Len" &&
        !this.target("Len", sc)
          ? at(hi.args, 0)
          : undefined;
      let pre = "";
      let inner = sc;
      let fcode = "";
      if (lenOf) {
        fcode = this.ex(lenOf, sc);
        const elem = this.fresh("e");
        inner = withMemo(fcode, elem);
        const b = body(inner);
        if (b.includes(elem)) pre = `const ${elem} = R.apply(${fcode}, ${v}); `;
        return `for (let ${i} = 1, ${h} = R.len(${fcode}); ${i} <= ${h}; ${i}++) { const ${v} = R.int(${i}); ${pre}${b} }`;
      }
      return `for (let ${i} = ${this.nu(lo, sc)}, ${h} = ${this.nu(hi, sc)}; ${i} <= ${h}; ${i}++) { const ${v} = R.int(${i}); ${body(sc)} }`;
    }
    if (s.k === "op" && s.op === "DOMAIN") {
      const f = this.fresh("f");
      const i = this.fresh("i");
      const a = this.fresh("a");
      const p = this.fresh("p");
      const elem = this.fresh("e");
      const fcode = this.ex(at(s.args, 0), sc);
      const b = body(withMemo(fcode, elem));
      const pre = b.includes(elem) ? `const ${elem} = ${p}[${a} + 2 * ${i} + 1]; ` : "";
      return `{ const ${f} = ${fcode}; const ${a} = R.funStart(${f}), ${p} = R.pool; for (let ${i} = 0, n = R.funSize(${f}); ${i} < n; ${i}++) { const ${v} = ${p}[${a} + 2 * ${i}]; ${pre}${b} } }`;
    }
    const xs = this.fresh("xs");
    const i = this.fresh("i");
    return `{ const ${xs} = R.elems(${this.ex(s, sc)}); for (let ${i} = 0; ${i} < ${xs}.length; ${i}++) { const ${v} = ${xs}[${i}]; ${body(sc)} } }`;
  }

  private iterBounds(
    bounds: Array<{ vars: string[]; set: Expr }>,
    sc: Scope,
    body: (sc: Scope) => string
  ): string {
    // Each bound's set is read in the scope that holds the earlier bounds.
    const flat: Array<{ name: string; set: Expr }> = [];
    for (const b of bounds) for (const v of b.vars) flat.push({ name: v, set: b.set });
    const go = (k: number, scope: Scope): string => {
      if (k === flat.length) return body(scope);
      const f = at(flat, k);
      const js = this.fresh("x");
      return this.iter(f.set, scope, js, (s2) => go(k + 1, this.bind(s2, f.name, js)));
    };
    return go(0, sc);
  }

  // ------------------------------------------------------------ actions
  private unchangedVars(e: Expr, sc: Scope): number[] {
    if (e.k === "tuple") return e.items.flatMap((x) => this.unchangedVars(x, sc));
    if (e.k === "id" && !this.lookup(e.name, sc)) {
      const vi = this.varIndex.get(e.name);
      if (vi !== undefined) return [vi];
      const def = this.defs.get(e.name);
      if (def && def.params.length === 0) return this.unchangedVars(def.body, sc);
    }
    throw new CompileError("UNCHANGED takes variables or a tuple of variables");
  }

  // The variable that `lhs = e` or `lhs \in S` assigns here, if any.
  private assignTarget(lhs: Expr, sc: Scope): number | undefined {
    const id = sc.init ? lhs : lhs.k === "prime" ? lhs.e : undefined;
    if (id?.k !== "id" || this.lookup(id.name, sc)) return undefined;
    return this.varIndex.get(id.name);
  }

  private withAssigned(sc: Scope, i: number, js: string): Scope {
    const nxt = sc.nxt.slice();
    nxt[i] = js;
    return { ...sc, nxt };
  }

  // Code for each way the action holds; k gives the code at each end.
  act(e: Expr, sc: Scope, k: (sc: Scope) => string): string {
    switch (e.k) {
      case "and": {
        const go = (i: number, s: Scope): string =>
          i === e.items.length ? k(s) : this.act(at(e.items, i), s, (s2) => go(i + 1, s2));
        return go(0, sc);
      }
      case "or":
        return e.items.map((x) => `{ ${this.act(x, sc, k)} }`).join("\n");
      case "quant":
        if (e.q === "E") {
          return this.iterBounds(e.bounds, sc, (s2) => this.act(e.body, s2, k));
        }
        break;
      case "if":
        return `if (${this.bo(e.c, sc)}) { ${this.act(e.t, sc, k)} } else { ${this.act(e.e, sc, k)} }`;
      case "let": {
        // A LET definition with no parameters and no prime is evaluated once
        // here; the others are substituted at each use.
        let scope = sc;
        let code = "";
        for (const d of e.defs) {
          if (d.params.length === 0 && !JSON.stringify(d.body).includes('"k":"prime"')) {
            const v = this.fresh("l");
            code += `const ${v} = ${this.ex(d.body, scope)}; `;
            scope = this.bind(scope, d.name, v);
          } else scope = this.letMacros([d], scope);
        }
        return `{ ${code}${this.act(e.body, scope, k)} }`;
      }
      case "id":
      case "call": {
        const b = this.lookup(e.name, sc);
        if (b?.k === "js") break;
        const t = this.target(e.name, sc);
        if (t) {
          // Arguments are evaluated once, before the body.
          const args = e.k === "call" ? e.args : [];
          let code = "";
          const bindings: Binding[] = args.map((a) => {
            const v = this.fresh("a");
            code += `const ${v} = ${this.ex(a, sc)}; `;
            return { k: "js", code: v };
          });
          return `{ ${code}${this.act(t.def.body, this.macroScope(t, bindings, sc), k)} }`;
        }
        break;
      }
      case "cover":
        return `COV[${e.slot}]++; ${k(sc)}`;
      case "op": {
        const lhs = at(e.args, 0);
        const rhs = (): Expr => at(e.args, 1);
        if (e.op === "=" || e.op === "\\in") {
          const i = this.assignTarget(lhs, sc);
          if (i !== undefined) {
            const have = sc.nxt[i];
            if (e.op === "=") {
              if (have) return `if (${have} === ${this.ex(rhs(), sc)}) { ${k(sc)} }`;
              if (sc.lazyAssign) return k(this.withAssigned(sc, i, `(${this.ex(rhs(), sc)})`));
              const v = this.fresh("n");
              return `{ const ${v} = ${this.ex(rhs(), sc)}; ${k(this.withAssigned(sc, i, v))} }`;
            }
            const v = this.fresh("n");
            if (have) return `if (${this.memberCode(have, rhs(), sc)}) { ${k(sc)} }`;
            return this.iter(rhs(), sc, v, (s2) => k(this.withAssigned(s2, i, v)));
          }
        }
        if (e.op === "UNCHANGED") {
          let s = sc;
          const checks: string[] = [];
          for (const i of this.unchangedVars(lhs, sc)) {
            const have = s.nxt[i];
            if (have) checks.push(`${have} === ${sc.cur[i]}`);
            else s = this.withAssigned(s, i, at(sc.cur, i));
          }
          const body = k(s);
          return checks.length ? `if (${checks.join(" && ")}) { ${body} }` : body;
        }
        break;
      }
    }
    const guard = this.bo(e, sc);
    if (guard === "false") return "";
    if (guard === "true" || sc.guards?.has(guard)) return k(sc);
    const guards = new Set(sc.guards);
    guards.add(guard);
    return `if (${guard}) { ${k({ ...sc, guards })} }`;
  }
}

export { TlaEvalError };
