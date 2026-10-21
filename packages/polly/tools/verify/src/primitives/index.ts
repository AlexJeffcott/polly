// Verification primitives for formal verification.
//
// `requires` / `ensures` are runtime no-ops in production: the caller
// evaluates the condition, the primitive discards it, and only the verifier
// reads the call. Under POLLY_CONTRACTS (set by `polly mutate`, or by hand)
// a false condition throws a ContractViolation instead, so every contract
// doubles as an assertion in whatever test drives its handler.

/**
 * POLLY_CONTRACTS: off (default) keeps requires/ensures as no-ops; "ensures"
 * makes a false postcondition throw; "all" makes a false precondition throw too.
 */
export type ContractsMode = "off" | "ensures" | "all";

export type ContractPrimitive = "requires" | "ensures";

/**
 * Where violations are recorded before they are thrown, so a harness can fail
 * a test even when the caller (the message bus) swallowed the throw. The
 * mutate preload and the BDD runner read this key; they repeat the string
 * because they import no module of this package.
 */
export const CONTRACT_VIOLATIONS_KEY = "__pollyContractViolations";

/** Read once at load; browser bundles have no `process`, so they stay off. */
function readContractsMode(): ContractsMode {
  const v =
    typeof process !== "undefined" && process.env ? process.env["POLLY_CONTRACTS"] : undefined;
  return v === "all" || v === "ensures" ? v : "off";
}

const MODE: ContractsMode = readContractsMode();

/** The mode this process runs under (read from POLLY_CONTRACTS at load). */
export function contractsMode(): ContractsMode {
  return MODE;
}

/**
 * A false `requires` / `ensures` under POLLY_CONTRACTS. The message starts
 * with a marker the mutate engine reads out of junit failure text:
 * `[polly-contract ensures /abs/handlers.ts:50] the author's message`.
 */
export class ContractViolation extends Error {
  override readonly name = "ContractViolation";
  constructor(
    readonly primitive: ContractPrimitive,
    /** `file:line` of the call, absolute. */
    readonly site: string,
    readonly contractMessage?: string
  ) {
    super(
      `[polly-contract ${primitive} ${site}]${contractMessage === undefined ? "" : ` ${contractMessage}`}`
    );
  }
}

const OWN_FILE = import.meta.url.startsWith("file://")
  ? decodeURIComponent(import.meta.url.slice("file://".length))
  : import.meta.url;
const FRAME = /\(?([^()\s]+):(\d+):\d+\)?\s*$/;

/**
 * `file:line` of the `requires` / `ensures` call: the first stack frame
 * outside this module. When this module is bundled with its caller every
 * frame is "own", so the fourth frame (callSite, violate, the primitive,
 * caller) is taken instead.
 */
function callSite(): string {
  const frames: { file: string; line: string }[] = [];
  for (const line of (new Error().stack ?? "").split("\n")) {
    const m = FRAME.exec(line);
    if (m?.[1] && m[2]) frames.push({ file: m[1], line: m[2] });
  }
  const outside = frames.find((f) => f.file !== OWN_FILE) ?? frames[3];
  return outside ? `${outside.file}:${outside.line}` : "unknown:0";
}

declare global {
  // An ambient global declaration — `var` is the only legal form here. Only
  // these primitives write the list; readers elsewhere treat it as unknown.
  var __pollyContractViolations: ContractViolation[] | undefined;
}

function violationList(): ContractViolation[] {
  const existing = globalThis[CONTRACT_VIOLATIONS_KEY];
  if (Array.isArray(existing)) return existing;
  const list: ContractViolation[] = [];
  globalThis[CONTRACT_VIOLATIONS_KEY] = list;
  return list;
}

function violate(primitive: ContractPrimitive, condition: boolean, message?: string): void {
  if (condition) return;
  if (MODE === "off" || (MODE === "ensures" && primitive === "requires")) return;
  const violation = new ContractViolation(primitive, callSite(), message);
  violationList().push(violation);
  throw violation;
}

/** Return every violation recorded since the last drain, and clear the list. */
export function drainContractViolations(): ContractViolation[] {
  const list = violationList();
  return list.splice(0, list.length);
}

/**
 * Assert a precondition that must be true when the handler executes.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLA+ assertion
 * Under POLLY_CONTRACTS=all: throws ContractViolation when false
 *
 * @example
 * messageBus.on("USER_LOGIN", (payload) => {
 *   requires(state.user.loggedIn === false, "User must not be logged in")
 *   state.user.loggedIn = true
 * })
 */
export function requires(condition: boolean, message?: string): void {
  // No-op unless POLLY_CONTRACTS is "all"; the verifier reads the call statically.
  violate("requires", condition, message);
}

/**
 * Assert a postcondition that must be true after the handler completes.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLA+ assertion
 * Under POLLY_CONTRACTS=ensures|all: throws ContractViolation when false
 *
 * @example
 * messageBus.on("USER_LOGIN", (payload) => {
 *   state.user.loggedIn = true
 *   ensures(state.user.loggedIn === true, "User must be logged in")
 * })
 */
export function ensures(condition: boolean, message?: string): void {
  // No-op unless POLLY_CONTRACTS is set; the verifier reads the call statically.
  violate("ensures", condition, message);
}

/**
 * Define a global invariant that must always hold.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLA+ invariant
 *
 * @example
 * invariant("UserIdConsistent", () =>
 *   state.user.loggedIn === false || state.user.id !== null
 * )
 */
export function invariant(_name: string, condition: () => boolean): void {
  // Runtime no-op - only used during verification
  // Name and condition are checked during static analysis only
  void condition;
}

/**
 * Assert that a value is within a valid range.
 *
 * @example
 * requires(inRange(todoCount, 0, 100), "Todo count must be 0-100")
 */
export function inRange(value: number, min: number, max: number): boolean {
  return value >= min && value <= max;
}

/**
 * Assert that a value is one of the allowed values.
 *
 * @example
 * requires(oneOf(state.user.role, ["admin", "user"]), "Role must be admin or user")
 */
export function oneOf<T>(value: T, allowed: T[]): boolean {
  return allowed.includes(value);
}

/**
 * Assert that an array has a specific length constraint.
 *
 * @example
 * requires(hasLength(state.todos, { max: 10 }), "Too many todos")
 */
export function hasLength(array: unknown[], constraint: { min?: number; max?: number }): boolean {
  if (constraint.min !== undefined && array.length < constraint.min) return false;
  if (constraint.max !== undefined && array.length > constraint.max) return false;
  return true;
}

/**
 * Declare state-level constraints for verification and optional runtime checking.
 * Maps message types to preconditions on state fields.
 *
 * The parser automatically wires these constraints to handlers during verification.
 * Optionally, constraints can be enforced at runtime by passing `{ runtime: true }`.
 *
 * @example
 * // Verification only (TLA+ generation)
 * const state = { loggedIn: false };
 *
 * $constraints("loggedIn", {
 *   USER_LOGOUT: { requires: "state.loggedIn === true", message: "Must be logged in" },
 *   BOOKMARK_ADD: { requires: "state.loggedIn === true", message: "Must be logged in" },
 * });
 *
 * @example
 * // Runtime enforcement (function predicates)
 * $constraints("loggedIn", {
 *   USER_LOGOUT: {
 *     requires: (state) => state.loggedIn === true,
 *     message: "Must be logged in to logout"
 *   },
 * }, { runtime: true });
 */
export function $constraints(
  stateField: string,
  constraints: Record<
    string,
    {
      requires?: string | ((state: unknown) => boolean);
      ensures?: string | ((state: unknown) => boolean);
      message?: string;
    }
  >,
  options?: { runtime?: boolean }
): void {
  // Register constraints for runtime checking if enabled
  if (options?.runtime) {
    // Import dynamically to avoid circular dependencies
    // This is safe because it only happens at runtime, not during static analysis
    // @ts-expect-error - Dynamic import path resolves correctly at runtime
    import("../../../src/shared/lib/constraints.js")
      .then(({ registerConstraints }) => {
        registerConstraints(stateField, constraints);
      })
      .catch(() => {
        // Silently ignore - constraints module may not be available during static analysis
      });
  }

  // For verification: Still a no-op at runtime
  // Parser extracts these and wires them to TLA+ handlers
}

/**
 * Declare a global state constraint that prunes structurally impossible states.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLC CONSTRAINT clause, discarding states
 * that violate the predicate from the exploration queue entirely.
 *
 * Unlike `invariant()` (which checks but still explores), `stateConstraint()`
 * prevents the model checker from ever reaching the pruned states.
 *
 * @example
 * stateConstraint("LeaderRequiresConnection", () =>
 *   !connectionState.value.isLeader || connectionState.value.status === "connected"
 * )
 */
export function stateConstraint(
  name: string,
  predicate: () => boolean,
  options?: { message?: string }
): void {
  void name;
  void predicate;
  void options;
}

/**
 * Cross-peer universal quantifier for use inside `requires` and
 * `ensures` predicates. The runtime is a no-op that simply runs the
 * predicate against a single dummy context (so the assertion never
 * triggers at runtime); the verifier recognizes the wrapper in
 * predicate source and emits a `\A peer \in Contexts \ {ctx} : (...)`
 * clause that asks TLC to check the inner predicate against every
 * other context.
 *
 * @example
 * ensures(
 *   forAllPeers(peer => peer.todos.value.length === todos.value.length),
 *   "every peer agrees on todo count"
 * );
 */
export function forAllPeers<TPeer>(predicate: (peer: TPeer) => boolean): boolean {
  void predicate;
  return true;
}

/**
 * Cross-peer existential quantifier for use inside `requires` and
 * `ensures` predicates. Runtime no-op; the verifier emits a
 * `\E peer \in Contexts \ {ctx} : (...)` clause.
 *
 * @example
 * ensures(
 *   somePeer(peer => peer.user.value.loggedIn === true),
 *   "at least one peer has a logged-in user"
 * );
 */
export function somePeer<TPeer>(predicate: (peer: TPeer) => boolean): boolean {
  void predicate;
  return true;
}

// Re-export for convenience
export const verify = {
  requires,
  ensures,
  invariant,
  inRange,
  oneOf,
  hasLength,
  $constraints,
  stateConstraint,
  forAllPeers,
  somePeer,
};
