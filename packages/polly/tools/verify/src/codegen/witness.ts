/**
 * The verify half of the BDD reachability witness (`polly verify --witness`).
 *
 * The BDD stratum (tools/bdd) reduces each scenario to its Then-predicate — the
 * post-state a passing scenario claims is reachable, in the runtime
 * `signal.field` dialect (e.g. `user.loggedIn === true && user.role ===
 * "admin"`). This module turns one such predicate into a TLC *reachability
 * witness* over the generated subsystem spec:
 *
 *   WitnessReachable == ~(\E ctx \in Contexts : <predicate over contextStates[ctx]>)
 *
 * The negation makes the witness an invariant TLC can refute:
 *   - TLC reports it *violated*  ⇒ a state satisfying the predicate is REACHABLE
 *     ⇒ the scenario describes a real outcome — honest. The counterexample
 *     trace IS the scenario's path through the model.
 *   - TLC explores fully with *no violation* ⇒ the predicate is UNREACHABLE
 *     ⇒ the scenario asserts a state the model proves impossible — it lies.
 *
 * Why a dedicated translator and not the handler-expression `tsExpressionToTLA`:
 * the BDD dialect drops the `.value` a handler expression carries
 * (`user.loggedIn`, not `user.value.loggedIn`) and a witness only ever needs a
 * flat conjunction of comparisons over state fields. A small, total translator
 * for that grammar is far more predictable than threading the 150-KB generator's
 * mesh/array machinery through a second entry point.
 */

import * as path from "node:path";
import type { CustomTLAPath } from "../config/types";

/** The single invariant every generated witness module declares. */
export const WITNESS_INVARIANT = "WitnessReachable";

/** Raised when a Then-predicate falls outside the witness grammar. */
export class WitnessTranslationError extends Error {}

/**
 * The two directions a witness can run. A `positive` witness (the default)
 * asserts a *desirable* outcome — it should be reachable. A `forbidden` witness
 * (tag `@forbidden`) asserts an *undesirable* state — it must be unreachable.
 * The TLC mechanism is identical (the negated existential); only the verdict
 * inverts, so the same `bddPredicateToTLA` / module / cfg serve both.
 */
export type WitnessPolarity = "positive" | "forbidden";

/** A scenario tagged `@forbidden` flips the witness into a safety check. */
export function witnessPolarity(tags: string[]): WitnessPolarity {
  return tags.includes("forbidden") ? "forbidden" : "positive";
}

export interface WitnessVerdict {
  /** Display status, distinct per polarity so a report never conflates them. */
  status: "reachable" | "unreachable" | "excluded" | "violated";
  /** Whether this verdict passes (a forbidden state being unreachable passes). */
  ok: boolean;
  message: string;
}

/**
 * Map a TLC reachability fact to a pass/fail verdict for the witness's polarity.
 * `reachable` is true when TLC violated the witness invariant — it found a state
 * satisfying the predicate.
 *
 *   positive  + reachable   → honest, the outcome happens            (pass)
 *   positive  + unreachable → the scenario lies                      (fail)
 *   forbidden + unreachable → the bad state is provably impossible   (pass)
 *   forbidden + reachable   → the bad state IS reachable, a defect   (fail)
 */
export function witnessVerdict(polarity: WitnessPolarity, reachable: boolean): WitnessVerdict {
  if (polarity === "forbidden") {
    return reachable
      ? {
          status: "violated",
          ok: false,
          message:
            "the forbidden state is REACHABLE — a defect; the counterexample is the path to it",
        }
      : { status: "excluded", ok: true, message: "the model proves this state unreachable" };
  }
  return reachable
    ? { status: "reachable", ok: true, message: "the model reaches this outcome" }
    : {
        status: "unreachable",
        ok: false,
        message: "the model proves this outcome impossible (the scenario lies)",
      };
}

/** JS comparison → TLA+ operator, longest-token-first so `===` wins over `==`. */
const COMPARATORS: ReadonlyArray<readonly [string, string]> = [
  ["===", "="],
  ["!==", "#"],
  ["==", "="],
  ["!=", "#"],
  [">=", ">="],
  ["<=", "<="],
  [">", ">"],
  ["<", "<"],
];

/** `user.loggedIn` → `user_loggedIn`; the signal name and nested fields join with `_`. */
function flattenField(path: string): string {
  return path.split(".").join("_");
}

/**
 * How a field reference renders in the target spec. The generated subsystem spec
 * keeps per-context state in `contextStates[ctx]`, so a field is read from there
 * (the default); a hand-written spec exposes its own top-level variables, so a
 * field maps straight to one (via {@link bareFieldRenderer}).
 */
export type FieldRenderer = (fieldPath: string) => string;

/** Field → `contextStates[ctx].<flattened>` — the generated-spec shape. */
const contextFieldRenderer: FieldRenderer = (fieldPath) =>
  `contextStates[ctx].${flattenField(fieldPath)}`;

/**
 * Field → a hand-written spec's own variable name. A `fields` entry maps the BDD
 * field name to the spec's TLA+ variable (e.g. `speaker` → `Speaker`); an
 * unmapped field falls back to the flattened name.
 */
export function bareFieldRenderer(fields: Record<string, string> = {}): FieldRenderer {
  return (fieldPath) => fields[fieldPath] ?? flattenField(fieldPath);
}

/**
 * Translate one operand. A literal (boolean/number/string) maps straight across;
 * a field reference is rendered by `render`, and a trailing `.length` becomes
 * TLA+ sequence length `Len(...)`.
 */
function translateOperand(raw: string, render: FieldRenderer): string {
  const op = raw.trim();
  if (op === "true") return "TRUE";
  if (op === "false") return "FALSE";
  if (/^"[^"]*"$/.test(op)) return op;
  if (/^'[^']*'$/.test(op)) return `"${op.slice(1, -1)}"`;
  if (/^[-+]?\d+(?:\.\d+)?$/.test(op)) return op;
  if (!/^[a-zA-Z_$][\w$]*(?:\.[a-zA-Z_$][\w$]*)*$/.test(op)) {
    throw new WitnessTranslationError(`unsupported operand "${raw}" in witness predicate`);
  }
  if (op.endsWith(".length")) {
    return `Len(${render(op.slice(0, -".length".length))})`;
  }
  return render(op);
}

/** Translate a single `lhs <op> rhs` comparison. */
function translateConjunct(conjunct: string, render: FieldRenderer): string {
  const text = conjunct.trim();
  for (const [js, tla] of COMPARATORS) {
    const at = text.indexOf(js);
    if (at === -1) continue;
    const lhs = text.slice(0, at);
    const rhs = text.slice(at + js.length);
    return `${translateOperand(lhs, render)} ${tla} ${translateOperand(rhs, render)}`;
  }
  throw new WitnessTranslationError(`no comparison operator in witness conjunct "${conjunct}"`);
}

/**
 * Translate a BDD Then-predicate (`&&`-joined comparisons, `signal.field`
 * dialect) into a TLA+ predicate. By default fields read from `contextStates[ctx]`
 * (the generated spec); pass a {@link bareFieldRenderer} to target a hand-written
 * spec's own variables instead.
 */
export function bddPredicateToTLA(
  predicate: string,
  render: FieldRenderer = contextFieldRenderer
): string {
  const conjuncts = predicate
    .split("&&")
    .map((c) => c.trim())
    .filter(Boolean);
  if (conjuncts.length === 0) {
    throw new WitnessTranslationError("empty witness predicate");
  }
  return conjuncts.map((c) => translateConjunct(c, render)).join(" /\\ ");
}

/**
 * Wrap a translated predicate as the negated-reachability witness invariant over
 * the generated spec's `Contexts` quantifier — TLC refutes it exactly when some
 * context reaches the predicate.
 */
export function buildWitnessInvariant(tlaPredicate: string): string {
  return `${WITNESS_INVARIANT} == ~(\\E ctx \\in Contexts : ${tlaPredicate})`;
}

/**
 * The hand-written-spec form: a plain state invariant over the spec's own
 * variables (no `Contexts` quantifier, which a generated spec has but an authored
 * state machine does not). TLC refutes it exactly when a reachable state matches.
 */
export function buildWitnessInvariantBare(tlaPredicate: string): string {
  return `${WITNESS_INVARIANT} == ~(${tlaPredicate})`;
}

/** Options for {@link buildWitnessModule}. */
export interface WitnessModuleOptions {
  /**
   * Target a hand-written spec: emit the bare invariant (no `Contexts`
   * quantifier) for a spec whose state is its own top-level variables.
   */
  bare?: boolean;
}

/**
 * A tiny TLA+ module that EXTENDS the base spec and adds the one witness
 * invariant. EXTENDS pulls in every definition the invariant needs — for a
 * generated spec `Contexts`, `contextStates`, `UserSpec`, `StateConstraint`; for
 * a hand-written one its own variables — so the witness stays non-invasive: the
 * base spec is never edited.
 */
export function buildWitnessModule(
  moduleName: string,
  baseModule: string,
  tlaPredicate: string,
  options: WitnessModuleOptions = {}
): string {
  const invariant = options.bare
    ? buildWitnessInvariantBare(tlaPredicate)
    : buildWitnessInvariant(tlaPredicate);
  return [
    `---- MODULE ${moduleName} ----`,
    `EXTENDS ${baseModule}`,
    "",
    invariant,
    "====",
    "",
  ].join("\n");
}

/** Parse the module name from a `.tla`'s `---- MODULE X ----` header, or null. */
export function parseModuleName(tlaText: string): string | null {
  const m = /^-+\s*MODULE\s+([A-Za-z_]\w*)/m.exec(tlaText);
  return m?.[1] ?? null;
}

/** Where a witness module + cfg are written, and which module it EXTENDS. */
export interface WitnessSpecLocation {
  /** Directory the witness module is written into (must hold the base module). */
  dir: string;
  /** Path to the base `.tla` the witness EXTENDS. */
  tlaPath: string;
  /** Path to the base `.cfg` the witness `.cfg` is derived from. */
  cfgPath: string;
  /** Module name the witness EXTENDS. */
  module: string;
  /** True when resolved from a hand-written spec (bare-variable predicate). */
  custom: boolean;
}

/**
 * Resolve where a subsystem's witness reads its base spec. With a `custom`
 * binding, the hand-written `.tla`/`.cfg` (relative to `cwd`) and its module
 * (`customModule`, already defaulted from {@link parseModuleName}); otherwise the
 * generated `UserApp_<subsystem>` under `specs/tla/generated/<subsystem>`.
 */
export function witnessSpecLocation(
  cwd: string,
  subsystem: string,
  custom: CustomTLAPath | undefined,
  customModule: string
): WitnessSpecLocation {
  if (custom) {
    const tlaPath = path.resolve(cwd, custom.tla);
    return {
      dir: path.dirname(tlaPath),
      tlaPath,
      cfgPath: path.resolve(cwd, custom.cfg),
      module: customModule,
      custom: true,
    };
  }
  const dir = path.join(cwd, "specs", "tla", "generated", subsystem);
  return {
    dir,
    tlaPath: path.join(dir, `UserApp_${subsystem}.tla`),
    cfgPath: path.join(dir, `UserApp_${subsystem}.cfg`),
    module: `UserApp_${subsystem}`,
    custom: false,
  };
}

/** The indented, non-comment body lines of a top-level `.cfg` section. */
function sectionBody(cfg: string, header: string): string[] {
  const body: string[] = [];
  let inSection = false;
  for (const line of cfg.split("\n")) {
    const headerMatch = /^([A-Z_]+)\b/.exec(line);
    if (headerMatch) {
      inSection = headerMatch[1] === header;
      continue;
    }
    if (!inSection) continue;
    if (line.trim() === "" || line.trim().startsWith("\\*")) continue;
    body.push(line);
  }
  return body;
}

/**
 * Constant assignments from a `.cfg`, tolerating every form TLC accepts: the
 * singular `CONSTANT` keyword as well as plural `CONSTANTS`, and assignments
 * given inline on the keyword line (`CONSTANT Controller = "safe"`) as well as
 * indented beneath a bare `CONSTANTS` header. Hand-written cfgs lean on the
 * inline singular form, which a plain `sectionBody(cfg, "CONSTANTS")` misses
 * entirely — dropping the binding and leaving TLC with an unassigned constant.
 * Output is normalised to indented body lines for a single `CONSTANTS` section.
 */
function constantBody(cfg: string): string[] {
  const body: string[] = [];
  let inSection = false;
  for (const line of cfg.split("\n")) {
    const headerMatch = /^([A-Z_]+)\b(.*)$/.exec(line);
    if (headerMatch) {
      const isConstant = headerMatch[1] === "CONSTANT" || headerMatch[1] === "CONSTANTS";
      inSection = isConstant;
      const inline = (headerMatch[2] ?? "").trim();
      if (isConstant && inline !== "") body.push(`  ${inline}`);
      continue;
    }
    if (!inSection) continue;
    if (line.trim() === "" || line.trim().startsWith("\\*")) continue;
    body.push(line);
  }
  return body;
}

/** The inline value of a single-line header (e.g. `SPECIFICATION UserSpec`). */
function headerLine(cfg: string, header: string): string | null {
  for (const line of cfg.split("\n")) {
    const m = new RegExp(`^${header}\\b(.*)$`).exec(line);
    if (m) return line.trimEnd();
  }
  return null;
}

/**
 * Derive a witness `.cfg` from a subsystem `.cfg`: keep SPECIFICATION,
 * CONSTANTS, CONSTRAINT and SYMMETRY verbatim, swap the INVARIANTS list for the
 * single witness, and drop PROPERTIES (the ensures temporal properties play no
 * part in — and only slow down — a state-reachability check). CONSTRAINT is
 * kept on purpose: StateConstraint prunes the space and is exactly what makes an
 * unreachable outcome provably unreachable (the login-guard case).
 */
export function buildWitnessCfg(baseCfg: string): string {
  // A generated spec names SPECIFICATION; a hand-written one may instead pair
  // INIT/NEXT. Carry whichever the base used so the witness drives the same
  // behaviour; fall back to the generated default.
  const spec = headerLine(baseCfg, "SPECIFICATION");
  const init = headerLine(baseCfg, "INIT");
  const next = headerLine(baseCfg, "NEXT");
  const behaviour = spec ? [spec] : init && next ? [init, next] : ["SPECIFICATION UserSpec"];
  const constants = constantBody(baseCfg);
  const constraint = sectionBody(baseCfg, "CONSTRAINT");
  const symmetry = sectionBody(baseCfg, "SYMMETRY");

  const out = [
    ...behaviour,
    "",
    "CONSTANTS",
    ...constants,
    "",
    "INVARIANTS",
    `  ${WITNESS_INVARIANT}`,
  ];
  if (constraint.length > 0) out.push("", "CONSTRAINT", ...constraint);
  if (symmetry.length > 0) out.push("", "SYMMETRY", ...symmetry);
  return `${out.join("\n")}\n`;
}

/** A field matches a subsystem state key if either is a dotted prefix of the other. */
function covers(stateKeys: string[], field: string): boolean {
  return stateKeys.some(
    (k) => k === field || field.startsWith(`${k}.`) || k.startsWith(`${field}.`)
  );
}

/**
 * Route a witness to the one subsystem whose state covers every field it
 * references. Returns the subsystem name, or `null` when no subsystem (or more
 * than one) owns the fields — a cross-subsystem outcome cannot be witnessed in
 * the compositional model, where each subsystem is checked in isolation.
 */
export function routeWitness(
  fields: string[],
  subsystems: Record<string, { state: string[] }>
): string | null {
  if (fields.length === 0) return null;
  const owners = Object.entries(subsystems).filter(([, sub]) =>
    fields.every((f) => covers(sub.state, f))
  );
  const only = owners.length === 1 ? owners[0] : undefined;
  return only ? only[0] : null;
}
