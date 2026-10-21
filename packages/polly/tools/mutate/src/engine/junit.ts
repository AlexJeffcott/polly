/**
 * Per-test results from `bun test --reporter=junit`, for matrix mode.
 *
 * Bun's XML nests one `<testsuite>` per file and one per `describe`; the
 * `classname` attribute lists the describe path innermost-first, so the full
 * name is rebuilt from the nesting instead. A test file that throws while
 * loading leaves no element at all — and so does a file with no tests. A file
 * the green baseline reported and a mutant run did not is a load failure;
 * `loadFailureId` names a stand-in test for it, so that mutant has a killer.
 *
 * One function, `testId`, builds the id for both the report's test list and
 * each mutant's `killedBy`, so the two always resolve against each other.
 */
import { realpathSync } from "node:fs";
import { relative, resolve } from "node:path";

export interface JunitCase {
  /** Absolute path of the test file. */
  file: string;
  /** describe path and test name, outermost first, joined with " > ". */
  name: string;
  /** The same path joined with spaces: the full name `bun test -t` matches. */
  filterName: string;
  line: number;
  status: "passed" | "failed" | "skipped";
  /** A failed case: the `<failure>` message attribute and body, decoded. */
  failureMessage?: string;
}

const ENTITIES: Record<string, string> = {
  "&quot;": '"',
  "&apos;": "'",
  "&lt;": "<",
  "&gt;": ">",
  "&amp;": "&",
};

function decode(s: string): string {
  return s.replace(/&(?:quot|apos|lt|gt|amp|#(\d+)|#x([0-9a-f]+));/gi, (m, dec, hex) => {
    if (dec) return String.fromCodePoint(Number(dec));
    if (hex) return String.fromCodePoint(Number.parseInt(hex, 16));
    return ENTITIES[m] ?? m;
  });
}

function attr(attrs: string, key: string): string {
  // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp — key is a callsite literal attribute name (name / file / line / message); [^"]* cannot backtrack.
  const m = new RegExp(`\\b${key}="([^"]*)"`).exec(attrs);
  return m?.[1] === undefined ? "" : decode(m[1]);
}

function caseStatus(body: string): JunitCase["status"] {
  if (/<(?:failure|error)\b/.test(body)) return "failed";
  return /<skipped\b/.test(body) ? "skipped" : "passed";
}

const FAILURE = /<(?:failure|error)\b([^>]*?)(?:\/>|>([\s\S]*?)<\/(?:failure|error)>)/;

/** The failure's message attribute, then its text, decoded; undefined when not failed. */
function failureMessage(body: string): string | undefined {
  const m = FAILURE.exec(body);
  if (!m) return undefined;
  const parts = [attr(m[1] ?? "", "message"), decode(m[2] ?? "")].filter((s) => s.length > 0);
  return parts.join("\n");
}

const TAG =
  /<testsuite\b([^>]*?)(\/?)>|<\/testsuite>|<testcase\b([^>]*?)(?:\/>|>([\s\S]*?)<\/testcase>)/g;

/** `cwd` is the directory `bun test` ran in: Bun writes `file` relative to it when it can. */
export function parseJunit(xml: string, cwd: string): JunitCase[] {
  const cases: JunitCase[] = [];
  // The first suite level is the file; deeper levels are describe blocks.
  const suites: string[] = [];
  for (const [whole, suiteAttrs, selfClosing, caseAttrs, body] of xml.matchAll(TAG)) {
    if (whole.startsWith("</testsuite")) suites.pop();
    else if (suiteAttrs !== undefined && selfClosing !== "/") suites.push(attr(suiteAttrs, "name"));
    else if (caseAttrs !== undefined) cases.push(caseFrom(suites, caseAttrs, body ?? "", cwd));
  }
  return cases;
}

function caseFrom(
  suites: readonly string[],
  caseAttrs: string,
  body: string,
  cwd: string
): JunitCase {
  const path = [...suites.slice(1), attr(caseAttrs, "name")];
  const status = caseStatus(body);
  const message = status === "failed" ? failureMessage(body) : undefined;
  return {
    file: resolve(cwd, attr(caseAttrs, "file")),
    name: path.join(" > "),
    filterName: path.join(" "),
    line: Number(attr(caseAttrs, "line")) || 0,
    status,
    ...(message === undefined ? {} : { failureMessage: message }),
  };
}

/** `<file relative to the project>#<full name>@<line>`. */
export function testId(projectCwd: string, file: string, name: string, line: number): string {
  return `${relative(projectCwd, file)}#${name}@${line}`;
}

/**
 * The marker a ContractViolation's message starts with (verify primitives):
 * `[polly-contract ensures /abs/handlers.ts:50] the author's message`.
 */
export const CONTRACT_MARKER = /\[polly-contract (requires|ensures) (.+?):(\d+)\]/g;

function realOr(path: string): string {
  try {
    return realpathSync(path);
  } catch {
    return path;
  }
}

/** Contract ids (`<file relative to the project>:<line>`) named in a failure text, sorted unique. */
export function contractsIn(text: string, projectCwd: string): string[] {
  const ids = new Set<string>();
  for (const m of text.matchAll(CONTRACT_MARKER)) {
    if (m[2] && m[3]) ids.add(`${relative(projectCwd, realOr(m[2]))}:${m[3]}`);
  }
  return [...ids].sort();
}

export interface ContractKill {
  /** junit.ts `testId` of the failed case. */
  test: string;
  contracts: string[];
}

/** Each failed case whose failure names a contract, with the contracts it names. */
export function contractKills(cases: readonly JunitCase[], projectCwd: string): ContractKill[] {
  const out: ContractKill[] = [];
  for (const c of cases) {
    if (c.status !== "failed" || c.failureMessage === undefined) continue;
    const contracts = contractsIn(c.failureMessage, projectCwd);
    if (contracts.length > 0) {
      out.push({ test: testId(projectCwd, c.file, c.name, c.line), contracts });
    }
  }
  return out;
}

export const LOAD_FAILURE_NAME = "(file produced no results)";

export function loadFailureId(projectCwd: string, file: string): string {
  return testId(projectCwd, file, LOAD_FAILURE_NAME, 0);
}

/**
 * The tests that detected a mutant: every failed case, plus a stand-in for
 * each file the baseline reported that this run did not (it threw while
 * loading, or the process died first). Empty when the process failed for a reason no test file explains.
 */
export function killers(
  cases: readonly JunitCase[],
  baselineFiles: ReadonlySet<string>,
  projectCwd: string
): string[] {
  const ids = cases
    .filter((c) => c.status === "failed")
    .map((c) => testId(projectCwd, c.file, c.name, c.line));
  const reported = new Set(cases.map((c) => c.file));
  for (const f of [...baselineFiles].sort()) {
    if (!reported.has(f)) ids.push(loadFailureId(projectCwd, f));
  }
  return ids;
}
