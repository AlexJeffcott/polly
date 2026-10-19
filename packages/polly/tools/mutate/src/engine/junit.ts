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
import { relative, resolve } from "node:path";

export interface JunitCase {
  /** Absolute path of the test file. */
  file: string;
  /** describe path and test name, outermost first, joined with " > ". */
  name: string;
  line: number;
  status: "passed" | "failed" | "skipped";
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
  const m = new RegExp(`\\b${key}="([^"]*)"`).exec(attrs);
  return m?.[1] === undefined ? "" : decode(m[1]);
}

function caseStatus(body: string): JunitCase["status"] {
  if (/<(?:failure|error)\b/.test(body)) return "failed";
  return /<skipped\b/.test(body) ? "skipped" : "passed";
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
    else if (caseAttrs !== undefined) {
      cases.push({
        file: resolve(cwd, attr(caseAttrs, "file")),
        name: [...suites.slice(1), attr(caseAttrs, "name")].join(" > "),
        line: Number(attr(caseAttrs, "line")) || 0,
        status: caseStatus(body ?? ""),
      });
    }
  }
  return cases;
}

/** `<file relative to the project>#<full name>@<line>`. */
export function testId(projectCwd: string, file: string, name: string, line: number): string {
  return `${relative(projectCwd, file)}#${name}@${line}`;
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
