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
import { PackedStateStore, StateCodec } from "./state-store";
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

/** How often the search loop reads the clock, in expanded states. */
const TIMEOUT_POLL = 4096;

/**
 * How often the search runs a full GC, in expanded states. JSC starts a full
 * collection at a size relative to the heap, and the stores' typed arrays
 * make that size large, so the short-lived objects the compiled actions make
 * pile up. On webrtc-p2p-chat/client (123,836,552 states) the run peaks at
 * 4.65 GB with this collection and at 7.18 GB without it. The heap holds few
 * live objects (15,788 at the end), so a full collection is cheap.
 */
const GC_EVERY = 1 << 20;

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
  store: PackedStateStore,
  violation: Violation
): string[] {
  const chain: Int32Array[] = [violation.state];
  // A deadlocked state is in the store already; its own entry starts the walk.
  for (let k = violation.parent; k >= 0; k = store.parent(k)) {
    chain.push(store.get(k, new Int32Array(vars.length)));
  }
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
  // The state being expanded, decoded from the store.
  const CUR = new Int32Array(n);
  const codec = new StateCodec(n);
  const store = new PackedStateStore(codec);
  const outside = new PackedStateStore(codec);
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
    const key = codec.encode(NX);
    if (recheck) {
      const inModel = p.constraint(NX);
      if (inModel && !store.add(key, expanding)) return;
      if (!violation) checkInvariants(p);
      return;
    }
    if (store.has(key)) return;
    if (outside.has(key)) {
      if (levelConstraint && p.constraint(NX)) store.add(key, expanding);
      return;
    }
    if (p.constraint(NX)) store.add(key, expanding);
    else outside.add(key, expanding);
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
  let sinceGc = 0;
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
      if (++sinceGc === GC_EVERY) {
        sinceGc = 0;
        Bun.gc(true);
      }
      expanding = k;
      const before = generated;
      compiled.next(store.get(k, CUR));
      if (generated === before && !violation) {
        // TLC reports the deadlocked state itself as the last trace state.
        violation = { what: "deadlock", state: CUR.slice(), parent: store.parent(k) };
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
