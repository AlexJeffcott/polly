/**
 * Shared types for the polly BDD runner.
 *
 * The keystone is {@link StepBinding}: one declaration that speaks BOTH layers.
 * Its `given`/`when`/`then` callbacks drive the *runtime* (the real factory bus
 * + state signals); its `message`/`stateExpr` strings are statically extracted
 * for the *verify* cross-link — exactly the dual-use trick `requires()`/
 * `ensures()` already use (a runtime no-op whose argument text is read by the
 * TLA+ codegen). See tools/bdd/README.md.
 */

/** The minimal slice of a polly MessageBus the runner drives. */
export interface BusLike {
  send: (
    payload: { type: string; [k: string]: unknown },
    options?: { target?: string | string[]; tabId?: number; timeout?: number }
  ) => Promise<unknown>;
}

/** The minimal slice of a preact-style signal the runner reads/resets. */
export interface SignalLike<T = unknown> {
  value: T;
}

/**
 * Per-scenario execution context handed to every step callback. The bus and
 * signals are the *real* ones the app uses; `vars` is scratch space for a
 * scenario (e.g. an id captured in a `When` and asserted in a `Then`).
 */
export interface World {
  bus: BusLike;
  signals: Record<string, SignalLike>;
  vars: Record<string, unknown>;
  /** Response returned by the most recent `bus.send` in a `When`. */
  lastResponse?: unknown;
  /** Error thrown by the most recent `When`, if any (for rejection asserts). */
  lastError?: unknown;
}

/**
 * A step callback: receives the world and the values captured from the text.
 * The return value is captured as `world.lastResponse` when not undefined — so
 * a `when` can simply `return world.bus.send(...)` and a later `then` asserts on
 * the response. `given`/`then` typically return nothing.
 */
export type StepFn = (world: World, ...args: string[]) => unknown;

/**
 * A step binding — declared once, read by two consumers.
 *
 * Runtime: the runner calls `given`/`when`/`then`.
 * Formal:  the verify extractor reads `message` (the message type a `when`
 *          sends) and `stateExpr` (the TS state expression a `given`/`then`
 *          establishes or asserts), turning the scenario into a trace it can
 *          check against the verification config and TLA+ model.
 */
export interface StepBinding {
  /** Cucumber-expression pattern, e.g. `the user logs in as {string}`. */
  pattern: string;
  given?: StepFn;
  when?: StepFn;
  then?: StepFn;
  /** Formal metadata: the message type a `when` step sends. */
  message?: string;
  /** Formal metadata: the TS state expression a `given`/`then` establishes/asserts. */
  stateExpr?: string;
}

/** How the app builds and cold-resets its real-factory world. */
export interface WorldDef {
  /** Build the world once per runner process (real factory + handlers). */
  create: () => World | Promise<World>;
  /** Cold-start reset run before every scenario (signals back to initial). */
  reset: (world: World) => void | Promise<void>;
}

// ── Parsed Gherkin (our normalized AST, decoupled from @cucumber/gherkin) ──

export type StepKeyword = "given" | "when" | "then";

export interface ParsedStep {
  /** Normalized keyword — And/But resolve to the previous concrete keyword. */
  keyword: StepKeyword;
  /** The raw keyword as written (Given/When/Then/And/But), for reporting. */
  rawKeyword: string;
  text: string;
  line: number;
}

export interface ParsedScenario {
  name: string;
  tags: string[];
  steps: ParsedStep[];
  line: number;
  /** True when expanded from a Scenario Outline row. */
  fromOutline?: boolean;
}

export interface ParsedFeature {
  name: string;
  description: string;
  tags: string[];
  /** Background steps prepended to every scenario, already keyword-normalized. */
  background: ParsedStep[];
  scenarios: ParsedScenario[];
  file: string;
}

// ── Run results ──

export type StepOutcome = "pass" | "fail" | "undefined" | "skipped";

export interface StepResult {
  text: string;
  rawKeyword: string;
  outcome: StepOutcome;
  message?: string;
}

export type ScenarioOutcome = "pass" | "fail" | "undefined" | "deferred-formal";

export interface ScenarioResult {
  feature: string;
  scenario: string;
  tags: string[];
  outcome: ScenarioOutcome;
  steps: StepResult[];
  file: string;
}

export interface RunResult {
  scenarios: ScenarioResult[];
  passed: number;
  failed: number;
  undefinedSteps: number;
  deferred: number;
  ok: boolean;
}

// ── Scenario trace (Phase 2: the verify cross-link) ──

/** A step matched to its binding's formal metadata. */
export interface TraceStep {
  text: string;
  keyword: StepKeyword;
  message?: string;
  stateExpr?: string;
  /** True when the step text matched no registered binding. */
  unbound?: boolean;
}

/**
 * A scenario reduced to the same vocabulary the verify config speaks:
 * Given (initial state exprs) → When (message types) → Then (state exprs).
 */
export interface ScenarioTrace {
  feature: string;
  scenario: string;
  tags: string[];
  given: TraceStep[];
  when: TraceStep[];
  then: TraceStep[];
  file: string;
}
