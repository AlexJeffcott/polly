/**
 * The mutant contract shared by the test preload (preload.ts) and the
 * bundler plugin (bundler-plugin.ts): POLLY_MUTATE_FILE is the absolute,
 * symlink-resolved path of the target, POLLY_MUTATE_SPAN the JSON
 * `{ start, end, replacement }` to swap into its text. Built-ins only, and
 * no side effects, so both entrypoints can import it.
 */

export interface MutantSpan {
  start: number;
  end: number;
  replacement: string;
}

export function loaderFor(file: string): "tsx" | "jsx" | "ts" | "js" {
  if (file.endsWith(".tsx")) return "tsx";
  if (file.endsWith(".jsx")) return "jsx";
  return /\.[cm]?ts$/.test(file) ? "ts" : "js";
}

export function exactly(paths: readonly string[]): RegExp {
  const escaped = paths.map((p) => p.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"));
  // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp — every path is escaped above; an anchored alternation of literals cannot backtrack exponentially.
  return new RegExp(`^(?:${escaped.join("|")})$`);
}

export function parseSpan(raw: string): MutantSpan {
  const value: unknown = JSON.parse(raw);
  if (
    typeof value === "object" &&
    value !== null &&
    "start" in value &&
    "end" in value &&
    "replacement" in value &&
    typeof value.start === "number" &&
    typeof value.end === "number" &&
    typeof value.replacement === "string"
  ) {
    return { start: value.start, end: value.end, replacement: value.replacement };
  }
  throw new Error(`polly mutate: malformed POLLY_MUTATE_SPAN: ${raw}`);
}

function newlines(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i++) if (s.charCodeAt(i) === 10) n++;
  return n;
}

/**
 * The mutated text, with the line count kept: a replacement that drops lines
 * (an emptied block, object or arrow body) is followed by a comment holding
 * them, so a contract after it still reports its own `file:line`.
 */
export function mutatedText(src: string, span: MutantSpan): string {
  const lost = newlines(src.slice(span.start, span.end)) - newlines(span.replacement);
  const pad = lost > 0 ? `/*${"\n".repeat(lost)}*/` : "";
  return src.slice(0, span.start) + span.replacement + pad + src.slice(span.end);
}
