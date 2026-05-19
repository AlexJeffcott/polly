/**
 * @fairfox/polly/test/e2e-mesh — canonical console-noise allowlist.
 *
 * Mesh runs emit a small number of benign console lines (Repo lifecycle,
 * Automerge warmup, occasional sync diagnostics). E2e scripts watch the
 * Puppeteer console stream and fail on anything unexpected; without an
 * allowlist every run trips on the same benign noise.
 *
 * The allowlist is owned by polly because polly knows which lines its
 * own code produces. Consumers extend it with their app-specific noise.
 * Entries are tested as substrings against the rendered console message.
 */

/** Match a console line that contains the given substring. */
export interface ConsolePattern {
  /** Optional console level filter — "log" | "info" | "warn" | "error".
   *  Undefined matches any level. */
  level?: "log" | "info" | "warn" | "error";
  /** Substring or RegExp the rendered console line must satisfy. */
  match: string | RegExp;
  /** Short reason — surfaces in failure messages when the allowlist
   *  evolves and an entry should be removed. */
  reason: string;
}

export const MESH_CONSOLE_ALLOWLIST: ReadonlyArray<ConsolePattern> = [
  {
    match: "[polly#107 H5]",
    reason:
      "polly#107 H5 warning fires whenever $meshState resolves against an unconfigured module instance during normal warmup; the issue tracks the longer fix.",
  },
  {
    match: "automerge",
    level: "log",
    reason: "Automerge logs its own version banner at log level on first import; benign.",
  },
  {
    match: "using deprecated parameters for `initSync()`",
    reason:
      "Automerge WASM bundler emits a deprecation warning on first init; upstream noise polly cannot suppress without a forked bundle.",
  },
  {
    match: "Failed to load resource",
    level: "error",
    reason:
      "Puppeteer logs a 404 for /favicon.ico against the in-tree consumer because the consumer does not ship one; the e2e harness only cares about app-level errors.",
  },
];

/**
 * Return true when the console line matches any allowlist entry.
 */
export function isAllowedConsoleLine(
  line: { level: string; text: string },
  allowlist: ReadonlyArray<ConsolePattern> = MESH_CONSOLE_ALLOWLIST
): boolean {
  for (const entry of allowlist) {
    if (entry.level && entry.level !== line.level) continue;
    if (typeof entry.match === "string") {
      if (line.text.includes(entry.match)) return true;
    } else if (entry.match.test(line.text)) {
      return true;
    }
  }
  return false;
}
