#!/usr/bin/env bun
// tlacheck.ts : explicit-state safety checker that reads the generated .tla
// and .cfg, as TLC does. Breadth-first, one level in memory at a time, with a
// 64-bit fingerprint per distinct state (TLC also keeps fingerprints only).
//
// Usage: bun tlacheck.ts --spec DIR [--module NAME]
// Prints: "N states generated, M distinct states found, depth D" (TLC's counts)
// Exit:   0 no error; 12 invariant violated or deadlock (TLC's code);
//         3 the spec uses TLA+ this checker does not support, or does not evaluate.

import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
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
  if (err instanceof Unsupported || err instanceof TlaSyntaxError || err instanceof EvalError) {
    console.log(`unsupported: ${err.message}`);
    process.exit(3);
  }
  throw err;
}
