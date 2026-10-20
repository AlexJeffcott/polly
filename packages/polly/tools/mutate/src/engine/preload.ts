/**
 * The engine's preload, passed to `bun test --preload` by the runner. Two modes.
 *
 * Mutant (POLLY_MUTATE_FILE + POLLY_MUTATE_SPAN): a Bun plugin whose onLoad
 * answers for exactly that file with the mutated text. Nothing is copied and
 * no other file is touched. With neither variable set it does nothing, which
 * is how the runner measures each target's baseline.
 *
 * Coverage (POLLY_MUTATE_COVERAGE, a plan written by coverage.ts): every
 * target loads with its probes (probes.ts), every test file loads behind a
 * marker import that names it, and global beforeEach/afterEach hooks split
 * the hits into buckets — while a file loads, inside each test (by ordinal),
 * and between tests. A global afterAll writes the buckets to
 * POLLY_MUTATE_COVERAGE_OUT; coverage.ts matches the ordinals to the junit
 * report. The marker is an import, not a statement, because a test file's
 * imports run before its first statement.
 *
 * A separate build entrypoint: the runner spawns it by path, so it must exist
 * as its own file in dist (see build-lib.ts). It imports only built-ins.
 *
 * CLI `--preload` adds to a bunfig `[test].preload`, so the project's own
 * preloads still run. One limit: a file that a project preload imports is
 * already loaded before this plugin registers, so it cannot be mutated.
 */
import { readFileSync, writeFileSync } from "node:fs";
import { plugin } from "bun";

const target = process.env["POLLY_MUTATE_FILE"];
const rawSpan = process.env["POLLY_MUTATE_SPAN"];
const coveragePlan = process.env["POLLY_MUTATE_COVERAGE"];
const coverageOut = process.env["POLLY_MUTATE_COVERAGE_OUT"];

function loaderFor(file: string): "tsx" | "jsx" | "ts" | "js" {
  if (file.endsWith(".tsx")) return "tsx";
  if (file.endsWith(".jsx")) return "jsx";
  return /\.[cm]?ts$/.test(file) ? "ts" : "js";
}

function exactly(paths: readonly string[]): RegExp {
  const escaped = paths.map((p) => p.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"));
  return new RegExp(`^(?:${escaped.join("|")})$`);
}

function parseSpan(raw: string): { start: number; end: number; replacement: string } {
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
  throw new Error(`polly mutate preload: malformed POLLY_MUTATE_SPAN: ${raw}`);
}

if (target && rawSpan) {
  const span = parseSpan(rawSpan);
  const src = await Bun.file(target).text();
  const contents = src.slice(0, span.start) + span.replacement + src.slice(span.end);
  const loader = loaderFor(target);
  plugin({
    name: "polly-mutate",
    setup(build) {
      build.onLoad({ filter: exactly([target]) }, () => ({ contents, loader }));
    },
  });
}

interface CoveragePlan {
  targets: { file: string; code: string }[];
  tests: string[];
}

function isStringList(v: unknown): v is string[] {
  return Array.isArray(v) && v.every((x) => typeof x === "string");
}

function parsePlan(raw: string): CoveragePlan {
  const value: unknown = JSON.parse(raw);
  if (
    typeof value === "object" &&
    value !== null &&
    "targets" in value &&
    "tests" in value &&
    Array.isArray(value.targets) &&
    isStringList(value.tests)
  ) {
    const targets: CoveragePlan["targets"] = [];
    for (const t of value.targets) {
      if (
        typeof t === "object" &&
        t !== null &&
        "file" in t &&
        "code" in t &&
        typeof t.file === "string" &&
        typeof t.code === "string"
      ) {
        targets.push({ file: t.file, code: t.code });
      } else throw new Error("polly mutate preload: malformed coverage plan target");
    }
    return { targets, tests: value.tests };
  }
  throw new Error("polly mutate preload: malformed coverage plan");
}

interface FileHits {
  load: Set<number>;
  between: Set<number>;
  tests: Set<number>[];
  /** A test began while another was running (concurrent tests): ordinals mean nothing. */
  overlapped: boolean;
}

if (coveragePlan && coverageOut) {
  const plan = parsePlan(readFileSync(coveragePlan, "utf8"));
  const { afterAll, afterEach, beforeEach } = await import("bun:test");
  const files: FileHits[] = plan.tests.map(() => ({
    load: new Set(),
    between: new Set(),
    tests: [],
    overlapped: false,
  }));
  const outside = new Set<number>();
  const served = new Set<number>();
  let current = outside;
  let file: FileHits | undefined;
  let running = 0;

  Object.assign(globalThis, {
    __pollyMutateHit(probe: number) {
      current.add(probe);
    },
    __pollyMutateFile(index: number) {
      file = files[index];
      running = 0;
      current = file?.load ?? outside;
    },
  });
  beforeEach(() => {
    if (!file) return;
    running++;
    if (running > 1) file.overlapped = true;
    const hits = new Set<number>();
    file.tests.push(hits);
    current = hits;
  });
  afterEach(() => {
    if (!file) return;
    running--;
    current = file.between;
  });
  afterAll(() => {
    const list = (s: Set<number>) => [...s];
    writeFileSync(
      coverageOut,
      JSON.stringify({
        served: list(served),
        outside: list(outside),
        files: files.map((f) => ({
          load: list(f.load),
          between: list(f.between),
          tests: f.tests.map(list),
          overlapped: f.overlapped,
        })),
      })
    );
  });

  const targetIndex = new Map(plan.targets.map((t, i) => [t.file, i]));
  const testIndex = new Map(plan.tests.map((t, i) => [t, i]));
  plugin({
    name: "polly-mutate-coverage",
    setup(build) {
      for (const i of testIndex.values()) {
        build.module(`polly-mutate-mark:${i}`, () => ({
          contents: `globalThis.__pollyMutateFile?.(${i});`,
          loader: "js",
        }));
      }
      // Synchronous on purpose: an async onLoad makes the module async, and
      // `require()` of an async module throws (mock.module factories use require).
      build.onLoad({ filter: exactly([...targetIndex.keys(), ...testIndex.keys()]) }, (args) => {
        const loader = loaderFor(args.path);
        const t = targetIndex.get(args.path);
        const planned = t === undefined ? undefined : plan.targets[t];
        if (t !== undefined && planned) {
          served.add(t);
          return { contents: planned.code, loader };
        }
        const src = readFileSync(args.path, "utf8");
        const mark = `import "polly-mutate-mark:${testIndex.get(args.path)}";`;
        // After a shebang line, and on the same line as the code: no line moves.
        const cut = src.startsWith("#!") ? src.indexOf("\n") + 1 : 0;
        return { contents: src.slice(0, cut) + mark + src.slice(cut), loader };
      });
    },
  });
}
