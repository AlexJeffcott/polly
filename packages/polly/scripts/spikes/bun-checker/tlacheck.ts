#!/usr/bin/env bun
// tlacheck.ts : explicit-state safety checker that reads the generated .tla
// and .cfg, as TLC does. Breadth-first, one level in memory at a time, with a
// 64-bit fingerprint per distinct state (TLC also keeps fingerprints only).
//
// Usage: bun tlacheck.ts --spec DIR [--module NAME] [--engine compiled|interp]
//   compiled (default): the spec compiled to JavaScript over interned values
//   interp:             the tree-walking interpreter (step 3a, the reference)
// Prints: "N states generated, M distinct states found, depth D" (TLC's counts)
// Exit:   0 no error; 12 invariant violated or deadlock (TLC's code);
//         3 the spec uses TLA+ this checker does not support, or does not evaluate.

import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { CompileError, type Compiled, compileSpec } from "./tla/compile";
import { type Ctx, Evaluator } from "./tla/eval";
import { TlaSyntaxError } from "./tla/lexer";
import { type Def, type Expr, parseModule } from "./tla/parser";
import { EvalError, key, ModelValue, mkSet, show, type Value } from "./tla/values";

const STANDARD_MODULES = new Set(["Integers", "Naturals", "Sequences", "FiniteSets", "TLC"]);

class Unsupported extends Error {}

type Cfg = {
  spec?: string;
  init?: string;
  next?: string;
  constants: Map<string, Value>;
  invariants: string[];
  constraints: string[];
  properties: string[];
};

function parseCfg(text: string): Cfg {
  const cfg: Cfg = { constants: new Map(), invariants: [], constraints: [], properties: [] };
  const lines = text.replace(/\\\*.*$/gm, "").replace(/\(\*[\s\S]*?\*\)/g, "").split("\n");
  let section = "";
  const value = (raw: string): Value => {
    const s = raw.trim();
    if (/^-?\d+$/.test(s)) return Number(s);
    if (s === "TRUE" || s === "FALSE") return s === "TRUE";
    if (/^".*"$/.test(s)) return s.slice(1, -1);
    if (s.startsWith("{") && s.endsWith("}")) {
      const inner = s.slice(1, -1).trim();
      return mkSet(inner === "" ? [] : inner.split(",").map(value));
    }
    if (/^[A-Za-z_]\w*$/.test(s)) return new ModelValue(s);
    throw new Unsupported(`cfg value ${s}`);
  };
  for (const raw of lines) {
    const line = raw.trim();
    if (line === "") continue;
    const head = /^([A-Z_]+)\b\s*(.*)$/.exec(line);
    if (head && /^(SPECIFICATION|INIT|NEXT|CONSTANTS?|INVARIANTS?|PROPERTY|PROPERTIES|CONSTRAINTS?|SYMMETRY|VIEW|ACTION_CONSTRAINTS?|CHECK_DEADLOCK|ALIAS|POSTCONDITION)$/.test(head[1] as string)) {
      section = head[1] as string;
      if (/^(SYMMETRY|VIEW|ACTION_CONSTRAINTS?|ALIAS|POSTCONDITION|CHECK_DEADLOCK)$/.test(section)) {
        throw new Unsupported(`cfg ${section}`);
      }
      const rest = (head[2] as string).trim();
      if (rest !== "") handle(rest);
      continue;
    }
    handle(line);
  }
  function handle(item: string) {
    switch (section) {
      case "SPECIFICATION":
        cfg.spec = item;
        return;
      case "INIT":
        cfg.init = item;
        return;
      case "NEXT":
        cfg.next = item;
        return;
      case "CONSTANT":
      case "CONSTANTS": {
        if (item.includes("<-")) throw new Unsupported(`cfg substitution ${item}`);
        const m = /^(\w+)\s*=\s*(.+)$/.exec(item);
        if (!m) throw new Unsupported(`cfg constant ${item}`);
        cfg.constants.set(m[1] as string, value(m[2] as string));
        return;
      }
      case "INVARIANT":
      case "INVARIANTS":
        cfg.invariants.push(...item.split(/\s+/));
        return;
      case "CONSTRAINT":
      case "CONSTRAINTS":
        cfg.constraints.push(...item.split(/\s+/));
        return;
      case "PROPERTY":
      case "PROPERTIES":
        cfg.properties.push(...item.split(/\s+/));
        return;
    }
    throw new Unsupported(`cfg line ${item}`);
  }
  return cfg;
}

function load(dir: string, name: string) {
  const defs = new Map<string, Def>();
  const constants: string[] = [];
  const vars: string[] = [];
  const loaded = new Set<string>();
  const visit = (mod: string) => {
    if (loaded.has(mod)) return;
    loaded.add(mod);
    const file = join(dir, `${mod}.tla`);
    if (!existsSync(file)) {
      if (STANDARD_MODULES.has(mod)) return;
      throw new Unsupported(`module ${mod}`);
    }
    const m = parseModule(readFileSync(file, "utf-8"), file);
    for (const ext of m.extends) visit(ext);
    constants.push(...m.constants);
    vars.push(...m.variables);
    for (const d of m.defs) defs.set(d.name, d);
  };
  visit(name);
  return { defs, constants, vars };
}

// Splits `Init /\ [][Next]_v /\ WF_v(Next)` into Init and Next.
function splitSpec(body: Expr, defs: Map<string, Def>): { init: Expr; next: Expr } {
  const items = body.k === "and" ? body.items : [body];
  const init: Expr[] = [];
  let next: Expr | undefined;
  const isFairness = (e: Expr): boolean =>
    (e.k === "call" && /^[WS]F_/.test(e.name)) || (e.k === "quant" && isFairness(e.body));
  for (const item of items) {
    if (item.k === "temporal" && item.op === "[]" && item.args[0]?.k === "actBox") next = item.args[0].a;
    else if (isFairness(item)) continue;
    else if (item.k === "id" && defs.get(item.name)?.body && containsTemporal(defs.get(item.name)?.body as Expr)) {
      const inner = splitSpec((defs.get(item.name) as Def).body, defs);
      init.push(inner.init);
      next = inner.next;
    } else init.push(item);
  }
  if (!next || init.length === 0) throw new Unsupported("SPECIFICATION is not Init /\\ [][Next]_v");
  return { init: init.length === 1 ? (init[0] as Expr) : { k: "and", items: init }, next };
}

function containsTemporal(e: Expr): boolean {
  if (e.k === "temporal" || e.k === "actBox") return true;
  if (e.k === "and") return e.items.some(containsTemporal);
  return false;
}

// Open-addressing set of 64-bit fingerprints. 0 marks an empty slot.
class FingerprintSet {
  private table = new BigUint64Array(1 << 20);
  private mask = (1 << 20) - 1;
  size = 0;
  add(fp: bigint): boolean {
    const f = fp === 0n ? 1n : fp;
    let i = Number(f & BigInt(this.mask));
    for (;;) {
      const v = this.table[i] as bigint;
      if (v === 0n) break;
      if (v === f) return false;
      i = (i + 1) & this.mask;
    }
    this.table[i] = f;
    this.size++;
    if (this.size * 2 > this.mask) this.grow();
    return true;
  }
  private grow() {
    const old = this.table;
    this.table = new BigUint64Array(old.length * 2);
    this.mask = this.table.length - 1;
    for (const v of old) {
      if (v === 0n) continue;
      let i = Number(v & BigInt(this.mask));
      while (this.table[i] !== 0n) i = (i + 1) & this.mask;
      this.table[i] = v;
    }
  }
}

// Exact set of state tuples (one Int32 ID per variable), kept in the order
// they were added: states [a, b) are one BFS level.
class StateStore {
  pool: Int32Array;
  count = 0;
  private table = new Int32Array(1 << 16).fill(-1);
  private mask = (1 << 16) - 1;
  constructor(private readonly width: number) {
    this.pool = new Int32Array(Math.max(1, width) << 16);
  }
  private hash(buf: Int32Array, off: number): number {
    let h = 0x9747b28c;
    for (let i = 0; i < this.width; i++) {
      let k = Math.imul(buf[off + i] as number, 0xcc9e2d51);
      k = (k << 15) | (k >>> 17);
      h ^= Math.imul(k, 0x1b873593);
      h = (h << 13) | (h >>> 19);
      h = (Math.imul(h, 5) + 0xe6546b64) | 0;
    }
    h ^= h >>> 16;
    h = Math.imul(h, 0x85ebca6b);
    h ^= h >>> 13;
    return h;
  }
  has(s: Int32Array): boolean {
    const w = this.width;
    let i = this.hash(s, 0) & this.mask;
    for (;;) {
      const k = this.table[i] as number;
      if (k < 0) return false;
      let same = true;
      for (let j = 0; j < w; j++) {
        if (this.pool[k * w + j] !== s[j]) {
          same = false;
          break;
        }
      }
      if (same) return true;
      i = (i + 1) & this.mask;
    }
  }
  // Adds s; false when it is already in the set.
  add(s: Int32Array): boolean {
    const w = this.width;
    let i = this.hash(s, 0) & this.mask;
    for (;;) {
      const k = this.table[i] as number;
      if (k < 0) break;
      let same = true;
      for (let j = 0; j < w; j++) {
        if (this.pool[k * w + j] !== s[j]) {
          same = false;
          break;
        }
      }
      if (same) return false;
      i = (i + 1) & this.mask;
    }
    if ((this.count + 1) * w > this.pool.length) {
      const p = new Int32Array(this.pool.length * 2);
      p.set(this.pool);
      this.pool = p;
    }
    this.pool.set(s, this.count * w);
    this.table[i] = this.count++;
    if (this.count * 2 > this.mask) this.grow();
    return true;
  }
  private grow() {
    this.table = new Int32Array(this.table.length * 2).fill(-1);
    this.mask = this.table.length - 1;
    for (let k = 0; k < this.count; k++) {
      let i = this.hash(this.pool, k * this.width) & this.mask;
      while ((this.table[i] as number) >= 0) i = (i + 1) & this.mask;
      this.table[i] = k;
    }
  }
  get(k: number): Int32Array {
    return this.pool.subarray(k * this.width, (k + 1) * this.width);
  }
}

function runCompiled(o: {
  defs: Map<string, Def>;
  constants: Map<string, Value>;
  vars: string[];
  init: Expr;
  next: Expr;
  constraints: Expr[];
  invariants: Array<{ name: string; e: Expr }>;
}): number {
  const t0 = performance.now();
  const n = o.vars.length;
  const NX = new Int32Array(n);
  const store = new StateStore(n);
  let generated = 0;
  let violation: { what: string; state: Int32Array; level: number } | undefined;
  let level = 1;
  // Set below; emit() runs only after compileSpec returns.
  let prog: Compiled | undefined;

  // TLC: a successor outside the constraint counts as generated and its
  // invariants are checked (tested: an invariant that only out-of-constraint
  // states break is reported), but it is not stored or expanded.
  //
  // A state already checked is not checked again: one in the visited set was
  // in the model and passed; one in `outside` passed while out of it. With a
  // constraint that reads TLCGet("level"), a state from `outside` gets the
  // constraint again, as the level has changed. Invariants that read the
  // level turn this off (`recheck`).
  const outside = new StateStore(n);
  let recheck = false;
  let levelConstraint = false;
  const checkInvariants = (p: Compiled) => {
    for (const inv of p.invariants) {
      if (!inv.holds(NX)) {
        violation = { what: `Invariant ${inv.name} is violated.`, state: NX.slice(), level };
        return;
      }
    }
  };
  const emit = () => {
    generated++;
    const p = prog as Compiled;
    if (recheck) {
      const inModel = p.constraint(NX);
      if (inModel && !store.add(NX)) return;
      if (!violation) checkInvariants(p);
      return;
    }
    if (store.has(NX)) return;
    if (outside.has(NX)) {
      if (levelConstraint && p.constraint(NX)) store.add(NX);
      return;
    }
    if (p.constraint(NX)) store.add(NX);
    else outside.add(NX);
    if (!violation) checkInvariants(p);
  };
  prog = compileSpec({ ...o, emit, nx: NX });
  recheck = prog.invariantsReadLevel;
  levelConstraint = prog.constraintReadsLevel;
  const tCompiled = performance.now();
  if (process.env["TLACHECK_DUMP"]) writeFileSync(process.env["TLACHECK_DUMP"], prog.source);

  // TLCGet("level") reads the level of the state being expanded (see
  // runInterp); init states read 1.
  prog.setLevel(1);
  prog.init();
  let start = 0;
  let depth = 0;
  while (start < store.count && !violation) {
    depth++;
    level = depth + 1;
    prog.setLevel(depth);
    const end = store.count;
    for (let k = start; k < end && !violation; k++) {
      const before = generated;
      prog.next(store.get(k));
      if (generated === before && !violation) violation = { what: "Deadlock reached.", state: store.get(k).slice(), level: depth };
    }
    start = end;
  }
  const t1 = performance.now();

  if (violation) {
    console.log(`Error: ${violation.what}`);
    o.vars.forEach((v, i) => console.log(`  ${v} = ${prog?.rt.show(violation?.state[i] as number)}`));
    depth = violation.level;
  }
  console.log(`${generated} states generated, ${store.count} distinct states found, depth ${depth}`);
  console.log(
    `wall ${((t1 - t0) / 1000).toFixed(3)} s (compile ${((tCompiled - t0) / 1000).toFixed(3)} s); rss ${(process.memoryUsage().rss / 2 ** 30).toFixed(2)} GiB; values ${prog.rt.count}`
  );
  return violation ? 12 : 0;
}

function main(): number {
  const args = process.argv.slice(2);
  const opt = (n: string) => {
    const i = args.indexOf(n);
    return i >= 0 ? args[i + 1] : undefined;
  };
  const dir = opt("--spec") ?? ".";
  const cfgs = readdirSync(dir).filter((f) => f.endsWith(".cfg") && !f.startsWith("Witness_"));
  const moduleName = opt("--module") ?? (cfgs.length === 1 ? (cfgs[0] as string).replace(/\.cfg$/, "") : undefined);
  if (!moduleName) throw new Unsupported(`${dir}: name the module with --module (found ${cfgs.length} .cfg files)`);

  const cfg = parseCfg(readFileSync(join(dir, `${moduleName}.cfg`), "utf-8"));
  const { defs, constants, vars } = load(dir, moduleName);
  for (const c of constants) if (!cfg.constants.has(c)) throw new Unsupported(`constant ${c} has no value in the cfg`);
  const ev = new Evaluator(defs, cfg.constants, vars);

  const defBody = (name: string): Expr => {
    const d = defs.get(name);
    if (!d || d.params.length > 0) throw new Unsupported(`no definition ${name} without parameters`);
    return d.body;
  };
  let init: Expr;
  let next: Expr;
  if (cfg.spec) ({ init, next } = splitSpec(defBody(cfg.spec), defs));
  else if (cfg.init && cfg.next) {
    init = defBody(cfg.init);
    next = defBody(cfg.next);
  } else throw new Unsupported("cfg names no SPECIFICATION and no INIT/NEXT");
  const invariants = cfg.invariants.map((n) => ({ name: n, e: defBody(n) }));
  const constraints = cfg.constraints.map(defBody);
  if (cfg.properties.length > 0) console.error(`note: PROPERTIES not checked (safety only): ${cfg.properties.join(", ")}`);

  const engine = opt("--engine") ?? "compiled";
  if (engine === "compiled") return runCompiled({ defs, constants: cfg.constants, vars, init, next, constraints, invariants });
  if (engine !== "interp") throw new Unsupported(`--engine ${engine}`);

  const n = vars.length;
  const seen = new FingerprintSet();
  let generated = 0;
  let frontier: Value[][] = [];
  let nextLevel: Value[][] = [];
  let violation: { what: string; state: Value[] } | undefined;

  // TLCGet("level") while TLC checks a successor reads the level of the state
  // being expanded, not the successor's: with `TLCGet("level") <= 4` TLC stores
  // states at level 5 (todo-list/preferences, depth 5). Init states read 1;
  // no spec yet tests that value.
  let level = 1;
  const stateCtx = (s: Value[]): Ctx => ({ cur: s, nxt: s, primed: false, init: false, env: null, level });
  const holds = (e: Expr, s: Value[]) => ev.evaluate(e, stateCtx(s)) === true;
  const check = (s: Value[]) => {
    for (const inv of invariants) if (!holds(inv.e, s)) return inv.name;
    return undefined;
  };
  // TLC: a state outside the constraint counts as generated and its
  // invariants are checked, but it is not stored or expanded.
  const visit = (s: Value[]) => {
    generated++;
    if (!constraints.every((c) => holds(c, s))) {
      const bad = check(s);
      if (bad && !violation) violation = { what: `Invariant ${bad} is violated.`, state: s };
      return;
    }
    const fp = Bun.hash(s.map(key).join("|")) as bigint;
    if (!seen.add(fp)) return;
    const bad = check(s);
    if (bad && !violation) violation = { what: `Invariant ${bad} is violated.`, state: s };
    nextLevel.push(s);
  };
  const complete = (nxt: Array<Value | undefined>): Value[] => {
    const s = nxt.slice() as Value[];
    for (let i = 0; i < n; i++) if (s[i] === undefined) throw new EvalError(`the step leaves ${vars[i]} unassigned`);
    return s;
  };

  const t0 = performance.now();
  const initState: Array<Value | undefined> = new Array(n).fill(undefined);
  ev.enumerate(init, { cur: initState, nxt: initState, primed: false, init: true, env: null }, (c) => {
    visit(complete(c.nxt));
    return false;
  });
  let depth = 0;
  while (nextLevel.length > 0 && !violation) {
    depth++;
    level = depth;
    frontier = nextLevel;
    nextLevel = [];
    for (const s of frontier) {
      const before = generated;
      const nxt: Array<Value | undefined> = new Array(n).fill(undefined);
      ev.enumerate(next, { cur: s, nxt, primed: false, init: false, env: null, level: depth }, (c) => {
        visit(complete(c.nxt));
        return violation !== undefined;
      });
      if (violation) break;
      if (generated === before) {
        violation = { what: "Deadlock reached.", state: s };
        break;
      }
    }
  }
  const secs = (performance.now() - t0) / 1000;

  if (violation) {
    console.log(`Error: ${violation.what}`);
    vars.forEach((v, i) => console.log(`  ${v} = ${show(violation?.state[i] as Value)}`));
  }
  console.log(`${generated} states generated, ${seen.size} distinct states found, depth ${depth}`);
  console.log(`wall ${secs.toFixed(3)} s; rss ${(process.memoryUsage().rss / 2 ** 30).toFixed(2)} GiB`);
  return violation ? 12 : 0;
}

try {
  process.exit(main());
} catch (err) {
  if (err instanceof Unsupported || err instanceof TlaSyntaxError || err instanceof EvalError || err instanceof CompileError) {
    console.log(`unsupported: ${err.message}`);
    process.exit(3);
  }
  throw err;
}
