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

/** The single invariant every generated witness module declares. */
export const WITNESS_INVARIANT = "WitnessReachable";

/** Raised when a Then-predicate falls outside the witness grammar. */
export class WitnessTranslationError extends Error {}

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
 * Translate one operand. A literal (boolean/number/string) maps straight across;
 * a field reference becomes `contextStates[ctx].<flattened>`, and a trailing
 * `.length` becomes TLA+ sequence length `Len(...)`.
 */
function translateOperand(raw: string): string {
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
    return `Len(contextStates[ctx].${flattenField(op.slice(0, -".length".length))})`;
  }
  return `contextStates[ctx].${flattenField(op)}`;
}

/** Translate a single `lhs <op> rhs` comparison. */
function translateConjunct(conjunct: string): string {
  const text = conjunct.trim();
  for (const [js, tla] of COMPARATORS) {
    const at = text.indexOf(js);
    if (at === -1) continue;
    const lhs = text.slice(0, at);
    const rhs = text.slice(at + js.length);
    return `${translateOperand(lhs)} ${tla} ${translateOperand(rhs)}`;
  }
  throw new WitnessTranslationError(`no comparison operator in witness conjunct "${conjunct}"`);
}

/**
 * Translate a BDD Then-predicate (`&&`-joined comparisons, `signal.field`
 * dialect) into a TLA+ predicate over `contextStates[ctx]`.
 */
export function bddPredicateToTLA(predicate: string): string {
  const conjuncts = predicate
    .split("&&")
    .map((c) => c.trim())
    .filter(Boolean);
  if (conjuncts.length === 0) {
    throw new WitnessTranslationError("empty witness predicate");
  }
  return conjuncts.map(translateConjunct).join(" /\\ ");
}

/** Wrap a translated predicate as the negated-reachability witness invariant. */
export function buildWitnessInvariant(tlaPredicate: string): string {
  return `${WITNESS_INVARIANT} == ~(\\E ctx \\in Contexts : ${tlaPredicate})`;
}

/**
 * A tiny TLA+ module that EXTENDS the generated subsystem spec and adds the one
 * witness invariant. EXTENDS pulls in every definition and declaration the
 * invariant needs (`Contexts`, `contextStates`, `UserSpec`, `StateConstraint`),
 * so the witness stays non-invasive — the subsystem spec is never edited.
 */
export function buildWitnessModule(
  moduleName: string,
  subsystemModule: string,
  tlaPredicate: string
): string {
  return [
    `---- MODULE ${moduleName} ----`,
    `EXTENDS ${subsystemModule}`,
    "",
    buildWitnessInvariant(tlaPredicate),
    "====",
    "",
  ].join("\n");
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
  const spec = headerLine(baseCfg, "SPECIFICATION") ?? "SPECIFICATION UserSpec";
  const constants = sectionBody(baseCfg, "CONSTANTS");
  const constraint = sectionBody(baseCfg, "CONSTRAINT");
  const symmetry = sectionBody(baseCfg, "SYMMETRY");

  const out = [spec, "", "CONSTANTS", ...constants, "", "INVARIANTS", `  ${WITNESS_INVARIANT}`];
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
