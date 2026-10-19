/**
 * The mutant-injection preload, passed to `bun test --preload` by the runner.
 *
 * With POLLY_MUTATE_FILE and POLLY_MUTATE_SPAN set, it registers a Bun plugin
 * whose onLoad answers for exactly that file with the mutated text. Nothing is
 * copied and no other file is touched. Without them it does nothing, which is
 * how the runner measures each target's baseline.
 *
 * A separate build entrypoint: the runner spawns it by path, so it must exist
 * as its own file in dist (see build-lib.ts). It imports nothing on purpose.
 *
 * CLI `--preload` adds to a bunfig `[test].preload`, so the project's own
 * preloads still run. One limit: a file that a project preload imports is
 * already loaded before this plugin registers, so it cannot be mutated.
 */
import { plugin } from "bun";

const target = process.env["POLLY_MUTATE_FILE"];
const rawSpan = process.env["POLLY_MUTATE_SPAN"];

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
  const loader = target.endsWith(".tsx")
    ? "tsx"
    : target.endsWith(".jsx")
      ? "jsx"
      : /\.[cm]?ts$/.test(target)
        ? "ts"
        : "js";
  const exact = new RegExp(`^${target.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}$`);
  plugin({
    name: "polly-mutate",
    setup(build) {
      build.onLoad({ filter: exact }, () => ({ contents, loader }));
    },
  });
}
