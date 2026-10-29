/**
 * The Bun safety checker: an explicit-state breadth-first search over the
 * generated `.tla` and `.cfg`, read as TLC reads them, with the spec compiled
 * to JavaScript (tla/compile.ts) over interned values (tla/runtime.ts).
 *
 * It checks what TLC checks for safety: the INVARIANTS under the CONSTRAINT,
 * and deadlock. It does not check PROPERTIES (temporal formulas); the caller
 * reports them as not checked. On the six spec sets in examples/ it gives
 * TLC's generated, distinct and depth counts exactly (`-workers 1`), at 2.5x
 * to 9x the speed of TLC `-workers auto` (scripts/spikes/bun-checker/README.md).
 *
 * TLC rules it keeps:
 * - A successor outside the CONSTRAINT counts as generated, not distinct; its
 *   invariants are checked; it is not expanded.
 * - `TLCGet("level")` while a successor is checked reads the level of the
 *   state being expanded; init states read 1.
 *
 * A construct it does not support gives `{ kind: "unsupported" }`, never a pass.
 */

import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { type Compiled, CompileError, compileSpec } from "./tla/compile";
import { TlaSyntaxError } from "./tla/lexer";
import { type Def, type Expr, parseModule } from "./tla/parser";
import { ModelValue, mkSet, TlaEvalError, type Value } from "./tla/values";

const STANDARD_MODULES = new Set(["Integers", "Naturals", "Sequences", "FiniteSets", "TLC"]);

/** A handler action, as the codegen names it and runner/handler-coverage.ts reads it. */
const HANDLER_ACTION = /^Handle\w+$/;

class Unsupported extends Error {}

export type CheckCounts = {
  generated: number;
  distinct: number;
  /** TLC's depth: the number of BFS levels, init states being level 1. */
  depth: number;
  /** Distinct init states in the model. */
  initial: number;
  /** States found but not expanded; non-zero only when the run stopped early. */
  leftOnQueue: number;
};

export type CheckResult =
  | {
      kind: "done";
      counts: CheckCounts;
      /** Times each handler action reached its last top-level conjunct. */
      handlerCounts: Map<string, number>;
      /** cfg PROPERTIES: temporal formulas this checker does not check. */
      properties: string[];
      seconds: number;
    }
  | {
      kind: "violation";
      what: "invariant" | "deadlock";
      /** The invariant, for `what: "invariant"`. */
      name?: string;
      /** TLC-style trace: `State N:` headers and `/\ var = value` lines. */
      trace: string[];
      counts: CheckCounts;
      properties: string[];
      seconds: number;
    }
  | { kind: "timeout"; counts: CheckCounts; properties: string[]; seconds: number }
  | { kind: "unsupported"; reason: string };

type Cfg = {
  spec?: string;
  init?: string;
  next?: string;
  constants: Map<string, Value>;
  invariants: string[];
  constraints: string[];
  properties: string[];
};

const CFG_SECTION =
  /^(SPECIFICATION|INIT|NEXT|CONSTANTS?|INVARIANTS?|PROPERTY|PROPERTIES|CONSTRAINTS?|SYMMETRY|VIEW|ACTION_CONSTRAINTS?|CHECK_DEADLOCK|ALIAS|POSTCONDITION)$/;
const CFG_UNSUPPORTED = /^(SYMMETRY|VIEW|ACTION_CONSTRAINTS?|ALIAS|POSTCONDITION|CHECK_DEADLOCK)$/;

function cfgValue(raw: string): Value {
  const s = raw.trim();
  if (/^-?\d+$/.test(s)) return Number(s);
  if (s === "TRUE" || s === "FALSE") return s === "TRUE";
  if (/^".*"$/.test(s)) return s.slice(1, -1);
  if (s.startsWith("{") && s.endsWith("}")) {
    const inner = s.slice(1, -1).trim();
    return mkSet(inner === "" ? [] : inner.split(",").map(cfgValue));
  }
  if (/^[A-Za-z_]\w*$/.test(s)) return new ModelValue(s);
  throw new Unsupported(`cfg value ${s}`);
}

export function parseCfg(text: string): Cfg {
  const cfg: Cfg = { constants: new Map(), invariants: [], constraints: [], properties: [] };
  const lines = text
    .replace(/\\\*.*$/gm, "")
    .replace(/\(\*[\s\S]*?\*\)/g, "")
    .split("\n");
  let section = "";
  const handle = (item: string): void => {
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
        if (!m?.[1] || !m[2]) throw new Unsupported(`cfg constant ${item}`);
        cfg.constants.set(m[1], cfgValue(m[2]));
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
  };
  for (const raw of lines) {
    const line = raw.trim();
    if (line === "") continue;
    const head = /^([A-Z_]+)\b\s*(.*)$/.exec(line);
    if (head?.[1] && CFG_SECTION.test(head[1])) {
      section = head[1];
      if (CFG_UNSUPPORTED.test(section)) throw new Unsupported(`cfg ${section}`);
      const rest = (head[2] ?? "").trim();
      if (rest !== "") handle(rest);
      continue;
    }
    handle(line);
  }
  return cfg;
}

function loadModules(dir: string, name: string) {
  const defs = new Map<string, Def>();
  const constants: string[] = [];
  const vars: string[] = [];
  const loaded = new Set<string>();
  const visit = (mod: string): void => {
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

function containsTemporal(e: Expr): boolean {
  if (e.k === "temporal" || e.k === "actBox") return true;
  if (e.k === "and") return e.items.some(containsTemporal);
  return false;
}

/** Splits `Init /\ [][Next]_v /\ WF_v(Next)` into Init and Next. */
function splitSpec(body: Expr, defs: Map<string, Def>): { init: Expr; next: Expr } {
  const items = body.k === "and" ? body.items : [body];
  const init: Expr[] = [];
  let next: Expr | undefined;
  const isFairness = (e: Expr): boolean =>
    (e.k === "call" && /^[WS]F_/.test(e.name)) || (e.k === "quant" && isFairness(e.body));
  for (const item of items) {
    if (isFairness(item)) continue;
    const named = item.k === "id" ? defs.get(item.name) : undefined;
    if (item.k === "temporal" && item.op === "[]" && item.args[0]?.k === "actBox") {
      next = item.args[0].a;
    } else if (named && containsTemporal(named.body)) {
      const inner = splitSpec(named.body, defs);
      init.push(inner.init);
      next = inner.next;
    } else init.push(item);
  }
  const [first] = init;
  if (!next || !first) throw new Unsupported("SPECIFICATION is not Init /\\ [][Next]_v");
  return { init: init.length === 1 ? first : { k: "and", items: init }, next };
}

/**
 * Puts a `cover` node into each handler action before its last top-level
 * conjunct: the conjunct TLC's `-coverage` count is read from
 * (runner/handler-coverage.ts). Conjunction runs left to right, so the node
 * is reached exactly at the states where every guard before it held.
 */
function instrumentHandlers(defs: Map<string, Def>): string[] {
  const actions: string[] = [];
  for (const def of defs.values()) {
    if (!HANDLER_ACTION.test(def.name)) continue;
    const cover: Expr = { k: "cover", slot: actions.length };
    actions.push(def.name);
    const items = def.body.k === "and" ? def.body.items : [def.body];
    const last = items.length - 1;
    def.body = { k: "and", items: [...items.slice(0, last), cover, ...items.slice(last)] };
  }
  return actions;
}

/**
 * Exact set of state tuples (one Int32 value ID per variable), kept in the
 * order they were added, so states [a, b) are one BFS level. Each state keeps
 * the index of the state it was reached from (-1 for an init state).
 */
class StateStore {
  pool: Int32Array;
  parents: Int32Array;
  count = 0;
  private table = new Int32Array(1 << 16).fill(-1);
  private mask = (1 << 16) - 1;
  constructor(private readonly width: number) {
    this.pool = new Int32Array(Math.max(1, width) << 16);
    this.parents = new Int32Array(1 << 16);
  }
  private hash(buf: Int32Array, off: number): number {
    let h = 0x9747b28c;
    for (let i = 0; i < this.width; i++) {
      let k = Math.imul(buf[off + i] ?? 0, 0xcc9e2d51);
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
  /** The slot holding s, or the empty slot where it would go (as -slot - 1). */
  private slot(s: Int32Array): number {
    const w = this.width;
    let i = this.hash(s, 0) & this.mask;
    for (;;) {
      const k = this.table[i] ?? -1;
      if (k < 0) return -i - 1;
      let same = true;
      for (let j = 0; j < w; j++) {
        if (this.pool[k * w + j] !== s[j]) {
          same = false;
          break;
        }
      }
      if (same) return i;
      i = (i + 1) & this.mask;
    }
  }
  has(s: Int32Array): boolean {
    return this.slot(s) >= 0;
  }
  /** Adds s, reached from `parent`; false when it is already in the set. */
  add(s: Int32Array, parent: number): boolean {
    const found = this.slot(s);
    if (found >= 0) return false;
    const w = this.width;
    if ((this.count + 1) * w > this.pool.length) {
      const p = new Int32Array(this.pool.length * 2);
      p.set(this.pool);
      this.pool = p;
    }
    if (this.count + 1 > this.parents.length) {
      const p = new Int32Array(this.parents.length * 2);
      p.set(this.parents);
      this.parents = p;
    }
    this.pool.set(s, this.count * w);
    this.parents[this.count] = parent;
    this.table[-found - 1] = this.count++;
    if (this.count * 2 > this.mask) this.grow();
    return true;
  }
  private grow(): void {
    this.table = new Int32Array(this.table.length * 2).fill(-1);
    this.mask = this.table.length - 1;
    for (let k = 0; k < this.count; k++) {
      let i = this.hash(this.pool, k * this.width) & this.mask;
      while ((this.table[i] ?? -1) >= 0) i = (i + 1) & this.mask;
      this.table[i] = k;
    }
  }
  get(k: number): Int32Array {
    return this.pool.subarray(k * this.width, (k + 1) * this.width);
  }
  parent(k: number): number {
    return this.parents[k] ?? -1;
  }
}

/** How often the search loop reads the clock, in expanded states. */
const TIMEOUT_POLL = 4096;

type Violation = {
  what: "invariant" | "deadlock";
  name?: string;
  state: Int32Array;
  /** Index in the store of the state it was reached from; -1 for an init state. */
  parent: number;
};

function traceLines(
  prog: Compiled,
  vars: string[],
  store: StateStore,
  violation: Violation
): string[] {
  const chain: Int32Array[] = [violation.state];
  // A deadlocked state is in the store already; its own entry starts the walk.
  for (let k = violation.parent; k >= 0; k = store.parent(k)) chain.push(store.get(k));
  chain.reverse();
  const lines: string[] = [];
  chain.forEach((state, i) => {
    lines.push(i === 0 ? "State 1: <Initial predicate>" : `State ${i + 1}:`);
    vars.forEach((v, j) => {
      lines.push(`/\\ ${v} = ${prog.rt.show(state[j] ?? 0)}`);
    });
  });
  return lines;
}

function search(o: {
  defs: Map<string, Def>;
  constants: Map<string, Value>;
  vars: string[];
  init: Expr;
  next: Expr;
  constraints: Expr[];
  invariants: Array<{ name: string; e: Expr }>;
  actions: string[];
  properties: string[];
  timeoutMs?: number;
}): CheckResult {
  const t0 = performance.now();
  const n = o.vars.length;
  const NX = new Int32Array(n);
  const cov = new Int32Array(o.actions.length);
  const store = new StateStore(n);
  const outside = new StateStore(n);
  let generated = 0;
  let violation: Violation | undefined;
  // The state being expanded: the parent of every successor emit() sees.
  let expanding = -1;
  let prog: Compiled | undefined;
  // A state already checked is not checked again: one in the store was in the
  // model and passed; one in `outside` passed while out of it. With a
  // constraint that reads TLCGet("level"), a state from `outside` gets the
  // constraint again, as the level has changed. Invariants that read the
  // level turn this off (`recheck`).
  let recheck = false;
  let levelConstraint = false;

  const checkInvariants = (p: Compiled): void => {
    for (const inv of p.invariants) {
      if (!inv.holds(NX)) {
        violation = { what: "invariant", name: inv.name, state: NX.slice(), parent: expanding };
        return;
      }
    }
  };
  const emit = (): void => {
    generated++;
    const p = prog;
    if (!p) throw new Error("internal: a state was emitted before the spec compiled");
    if (recheck) {
      const inModel = p.constraint(NX);
      if (inModel && !store.add(NX, expanding)) return;
      if (!violation) checkInvariants(p);
      return;
    }
    if (store.has(NX)) return;
    if (outside.has(NX)) {
      if (levelConstraint && p.constraint(NX)) store.add(NX, expanding);
      return;
    }
    if (p.constraint(NX)) store.add(NX, expanding);
    else outside.add(NX, expanding);
    if (!violation) checkInvariants(p);
  };

  const compiled = compileSpec({ ...o, emit, nx: NX, cov });
  prog = compiled;
  recheck = compiled.invariantsReadLevel;
  levelConstraint = compiled.constraintReadsLevel;

  compiled.setLevel(1);
  compiled.init();
  const initial = store.count;
  let start = 0;
  let depth = store.count > 0 ? 1 : 0;
  let expanded = 0;
  let timedOut = false;
  while (start < store.count && !violation && !timedOut) {
    compiled.setLevel(depth);
    const end = store.count;
    for (let k = start; k < end && !violation; k++) {
      if (o.timeoutMs !== undefined && ++expanded % TIMEOUT_POLL === 0) {
        if (performance.now() - t0 > o.timeoutMs) {
          timedOut = true;
          start = k;
          break;
        }
      }
      expanding = k;
      const before = generated;
      compiled.next(store.get(k));
      if (generated === before && !violation) {
        // TLC reports the deadlocked state itself as the last trace state.
        violation = { what: "deadlock", state: store.get(k).slice(), parent: store.parent(k) };
      }
    }
    if (timedOut) break;
    start = end;
    if (store.count > end) depth++;
  }

  const seconds = (performance.now() - t0) / 1000;
  const counts: CheckCounts = {
    generated,
    distinct: store.count,
    depth,
    initial,
    leftOnQueue: store.count - start,
  };
  if (violation) {
    const trace = traceLines(compiled, o.vars, store, violation);
    return {
      kind: "violation",
      what: violation.what,
      ...(violation.name === undefined ? {} : { name: violation.name }),
      trace,
      // TLC's depth for a violation is the length of its trace.
      counts: { ...counts, depth: trace.filter((l) => l.startsWith("State ")).length },
      properties: o.properties,
      seconds,
    };
  }
  if (timedOut) return { kind: "timeout", counts, properties: o.properties, seconds };
  const handlerCounts = new Map(o.actions.map((a, i) => [a, cov[i] ?? 0]));
  return {
    kind: "done",
    counts: { ...counts, leftOnQueue: 0 },
    handlerCounts,
    properties: o.properties,
    seconds,
  };
}

/**
 * Checks `<moduleName>.tla` under `<moduleName>.cfg` in `specDir`. Never
 * throws for a spec it cannot handle: that is `{ kind: "unsupported" }`.
 */
export function checkSpec(opts: {
  specDir: string;
  moduleName: string;
  timeoutMs?: number;
}): CheckResult {
  try {
    const cfg = parseCfg(readFileSync(join(opts.specDir, `${opts.moduleName}.cfg`), "utf-8"));
    const { defs, constants, vars } = loadModules(opts.specDir, opts.moduleName);
    for (const c of constants) {
      if (!cfg.constants.has(c)) throw new Unsupported(`constant ${c} has no value in the cfg`);
    }
    const defBody = (name: string): Expr => {
      const d = defs.get(name);
      if (!d || d.params.length > 0) {
        throw new Unsupported(`no definition ${name} without parameters`);
      }
      return d.body;
    };
    let init: Expr;
    let next: Expr;
    if (cfg.spec) ({ init, next } = splitSpec(defBody(cfg.spec), defs));
    else if (cfg.init && cfg.next) {
      init = defBody(cfg.init);
      next = defBody(cfg.next);
    } else throw new Unsupported("cfg names no SPECIFICATION and no INIT/NEXT");
    const invariants = cfg.invariants.map((name) => ({ name, e: defBody(name) }));
    const constraints = cfg.constraints.map(defBody);
    const actions = instrumentHandlers(defs);
    return search({
      defs,
      constants: cfg.constants,
      vars,
      init,
      next,
      constraints,
      invariants,
      actions,
      properties: cfg.properties,
      ...(opts.timeoutMs === undefined ? {} : { timeoutMs: opts.timeoutMs }),
    });
  } catch (err) {
    if (
      err instanceof Unsupported ||
      err instanceof TlaSyntaxError ||
      err instanceof TlaEvalError ||
      err instanceof CompileError
    ) {
      return { kind: "unsupported", reason: err.message };
    }
    throw err;
  }
}
