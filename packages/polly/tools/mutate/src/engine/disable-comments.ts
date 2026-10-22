/**
 * Disable comments: Stryker's syntax, read so a Stryker project's comments
 * keep working, plus a `polly-mutate` spelling of the same thing.
 *
 *   // Stryker disable next-line ObjectLiteral: a data table
 *   // Stryker disable all: generated code
 *   // Stryker restore all
 *   // polly-mutate disable next-line ArrowFunction,BlockStatement: reason
 *
 * Line and block comments both count. `next-line` covers the line after the
 * comment; without it the comment covers every later line until a `restore`
 * names the mutator. Mutator names ignore case; `all` names every mutator.
 * A mutant is covered when its span starts on a covered line — the rule
 * Stryker applies to the node's start line.
 *
 * generate.ts marks a covered mutant Ignored, with the comment's reason (or a
 * default naming the line) as its statusReason, the way polly#143 marks
 * verify callsites.
 */
import { MUTATOR_NAMES, type MutatorName } from "./types.ts";

const KNOWN = new Set([...MUTATOR_NAMES].map((n) => n.toLowerCase()));

export interface DisableComment {
  /** 1-based line the comment starts on. */
  line: number;
  /** Offset just past the comment; it rules only mutants after this. */
  end: number;
  action: "disable" | "restore";
  /** `next-line`: the one line after the comment. Otherwise the rest of the file. */
  from: number;
  to: number;
  /** Lower-cased mutator names, or null for `all`. */
  mutators: Set<string> | null;
  /** Names that match no mutator (a typo covers nothing). */
  unknown: string[];
  /** The text after the colon, else a default that names the comment's line. */
  reason: string;
}

interface Comment {
  type: string;
  value: string;
  start: number;
  end: number;
}

const DIRECTIVE =
  /^\s*\*?\s*(?:Stryker|polly-mutate)\s+(disable|restore)(\s+next-line)?\s+([A-Za-z]+(?:\s*,\s*[A-Za-z]+)*)\s*(?::([\s\S]*))?$/;

export function parseDisableComments(
  comments: readonly Comment[],
  lineOf: (offset: number) => number
): DisableComment[] {
  const out: DisableComment[] = [];
  for (const c of comments) {
    const match = DIRECTIVE.exec(c.value);
    if (!match) continue;
    const [, action, nextLine, list = "", rawReason] = match;
    const names = list.split(",").map((n) => n.trim());
    const all = names.some((n) => n.toLowerCase() === "all");
    const line = lineOf(c.start);
    const after = lineOf(c.end) + 1;
    const reason = rawReason?.replace(/\s+/g, " ").trim();
    out.push({
      line,
      end: c.end,
      action: action === "restore" ? "restore" : "disable",
      from: nextLine ? after : line,
      to: nextLine ? after : Number.POSITIVE_INFINITY,
      mutators: all ? null : new Set(names.map((n) => n.toLowerCase())),
      unknown: names.filter((n) => n.toLowerCase() !== "all" && !KNOWN.has(n.toLowerCase())),
      reason: reason || `Disabled by the comment on line ${line}`,
    });
  }
  return out;
}

/**
 * The disable comment covering a mutant that starts at `offset` on `line`:
 * the last comment before it that is in effect on that line and names its
 * mutator, unless that comment is a `restore`.
 */
export function disabledBy(
  comments: readonly DisableComment[],
  offset: number,
  line: number,
  mutatorName: MutatorName
): DisableComment | undefined {
  const name = mutatorName.toLowerCase();
  for (let i = comments.length - 1; i >= 0; i--) {
    const c = comments[i];
    if (!c || c.end > offset || line < c.from || line > c.to) continue;
    if (c.mutators && !c.mutators.has(name)) continue;
    return c.action === "disable" ? c : undefined;
  }
  return undefined;
}
