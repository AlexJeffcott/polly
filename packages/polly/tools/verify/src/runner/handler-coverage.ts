/**
 * Which generated handler actions TLC actually took.
 *
 * A handler whose `requires` guards are never all true at a reachable state is
 * never taken. Every `ensures` on it then holds vacuously, and the run reports
 * a pass for code the model never executed. examples/minimal (no handler set
 * `user.active`, so `HandlePing` was dead) and examples/full-featured (three
 * handlers guarded on a field no handler wrote) both passed this way.
 *
 * TLC's `-coverage` report counts, per source line, how often each expression
 * was evaluated. The codegen emits every handler as
 *
 *     HandleX(ctx) ==
 *       /\ <guard>
 *       /\ <guard>
 *       /\ <effect>
 *
 * and conjunction is evaluated left to right, so the effect conjunct is
 * evaluated only at states where every guard held. Its count is the reading:
 * 0 means the handler never ran.
 *
 * The reading is taken from the spec text rather than recorded by the codegen,
 * so a hand-edited or custom spec is read by the same rule.
 */

export type HandlerCoverage = {
  /** The TLA+ action name, e.g. `HandlePing`. */
  action: string;
  /** 1-based line of the action's last top-level conjunct. */
  effectLine: number;
  /** Times TLC evaluated that conjunct. */
  count: number;
  /**
   * False when no message type in `UserMessageTypes` dispatches to the action:
   * `messages.include` / `exclude` left it out, so the router never sends it
   * and a count of 0 is the configuration, not a defect.
   */
  inModel: boolean;
};

/** TLC's header for a coverage block. Absent when the run was not given `-coverage`. */
const COVERAGE_HEADER = /^The coverage statistics at /m;

/** One coverage entry: start line, module, count. Nested entries carry a `|` prefix. */
const COVERAGE_ENTRY = /^\s*\|*line (\d+), col \d+ to line \d+, col \d+ of module (\w+): (\d+)/gm;

const HANDLER_DEF = /^(Handle\w+)\(ctx\)\s*==\s*$/;

/**
 * The line of each handler's last top-level conjunct, keyed by action name.
 *
 * A body runs from the definition line to the first blank line. Top-level
 * conjuncts are the `/\` lines at the body's smallest `/\` indentation; deeper
 * ones sit inside an `\E` and are evaluated only when it is.
 */
export function handlerEffectLines(spec: string): Map<string, number> {
  const lines = spec.split("\n");
  const effects = new Map<string, number>();

  for (let i = 0; i < lines.length; i++) {
    const def = HANDLER_DEF.exec(lines[i] ?? "");
    if (!def?.[1]) continue;
    const body = bodyConjuncts(lines, i + 1);
    i = body.end;
    const top = Math.min(...body.conjuncts.map((c) => c.indent));
    const last = body.conjuncts.filter((c) => c.indent === top).at(-1);
    if (last) effects.set(def[1], last.line);
  }

  return effects;
}

/** The `/\` lines of a body starting at index `start`, and the index of its closing blank line. */
function bodyConjuncts(
  lines: string[],
  start: number
): { conjuncts: Array<{ line: number; indent: number }>; end: number } {
  const conjuncts: Array<{ line: number; indent: number }> = [];
  let end = start;
  for (; end < lines.length; end++) {
    const text = lines[end] ?? "";
    if (text.trim() === "") break;
    const conjunct = /^(\s+)\/\\/.exec(text);
    if (conjunct?.[1]) conjuncts.push({ line: end + 1, indent: conjunct[1].length });
  }
  return { conjuncts, end };
}

/**
 * The actions the router can reach: those `StateTransition` dispatches to from
 * a message type in `UserMessageTypes`. `undefined` when the spec declares no
 * `UserMessageTypes` (a hand-written spec), in which case every action counts.
 */
function actionsInModel(spec: string): Set<string> | undefined {
  const declared = /^UserMessageTypes == \{(.*)\}\s*$/m.exec(spec);
  if (!declared) return undefined;
  const types = new Set([...(declared[1] ?? "").matchAll(/"([^"]*)"/g)].map((m) => m[1]));
  const actions = new Set<string>();
  for (const m of spec.matchAll(/msgType = "([^"]*)" THEN (Handle\w+)\(ctx\)/g)) {
    if (m[2] && types.has(m[1])) actions.add(m[2]);
  }
  return actions;
}

/**
 * Per-line evaluation counts for `moduleName`, from TLC's coverage blocks.
 *
 * A line appears once for each action that reaches it, and again in each
 * periodic block, so the largest count is kept. Only "was it ever evaluated"
 * is read from it.
 */
function lineCounts(output: string, moduleName: string): Map<number, number> {
  const counts = new Map<number, number>();
  for (const m of output.matchAll(COVERAGE_ENTRY)) {
    if (m[2] !== moduleName) continue;
    const line = Number(m[1]);
    counts.set(line, Math.max(counts.get(line) ?? 0, Number(m[3])));
  }
  return counts;
}

/**
 * The coverage of every handler action in `spec`, or `undefined` when the TLC
 * output carries no coverage block (run without `-coverage`, or killed before
 * the end-of-run report).
 */
export function parseHandlerCoverage(
  spec: string,
  moduleName: string,
  output: string
): HandlerCoverage[] | undefined {
  if (!COVERAGE_HEADER.test(output)) return undefined;
  const counts = lineCounts(output, moduleName);
  const reachable = actionsInModel(spec);
  return [...handlerEffectLines(spec)].map(([action, effectLine]) => ({
    action,
    effectLine,
    count: counts.get(effectLine) ?? 0,
    inModel: reachable?.has(action) ?? true,
  }));
}

/** The handler actions in the model that TLC never took. */
export function neverTaken(coverage: HandlerCoverage[]): string[] {
  return coverage.filter((c) => c.inModel && c.count === 0).map((c) => c.action);
}
