/**
 * `polly mutate migrate [--write]` — turn a `stryker.conf.json` into a
 * `polly.mutate.ts`. The same mapping (`strykerToMutation`) is how the CLI
 * still reads a Stryker config it finds without a `polly.mutate.ts`, so the
 * fallback and the migrated file mean the same thing.
 *
 *   mutate                    → targets
 *   bun.testFiles             → tests.include
 *   bun.nodeArgs --preload    → tests.preload
 *   testRunner "command"      → runner { kind: "command", argv }
 *   concurrency               → concurrency
 *   timeoutFactor, timeoutMS  → timeout { factor, extraMs }
 *   disableBail               → mode "matrix"
 *   mutator.excludedMutations → mutators.exclude
 *   thresholds.break          → thresholds.break
 *
 * Everything else (plugins, ignorers, reporters, coverageAnalysis, …) is
 * Stryker machinery with no engine counterpart; each dropped key is listed
 * in the notes so nothing disappears silently.
 */
import { existsSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { isRecord } from "../../../src/shared/lib/guards";
import {
  MUTATION_CONFIG_FILE,
  type MutationConfig,
  type MutationTests,
  parseMutationConfig,
} from "./define.ts";

/** Stryker keys that are fully mapped; anything else is reported as dropped. */
const MAPPED = new Set([
  "mutate",
  "testRunner",
  "bun",
  "commandRunner",
  "concurrency",
  "timeoutFactor",
  "timeoutMS",
  "disableBail",
  "mutator",
  "thresholds",
  "ignorers",
]);
/** Keys that carry no meaning to keep — dropped without a note. */
const SILENT = new Set(["$schema", "_comment"]);
const SHELL_SYNTAX = /[|&;<>()$`"'\\*?{}[\]~]/;

export interface Migration {
  config: MutationConfig;
  notes: string[];
}

/** `--preload <p>` / `--preload=<p>` values from the bun runner's `nodeArgs`, as written. */
export function preloadArgs(nodeArgs: string[]): string[] {
  const out: string[] = [];
  nodeArgs.forEach((arg, i) => {
    const value =
      arg === "--preload"
        ? nodeArgs[i + 1]
        : arg.startsWith("--preload=")
          ? arg.slice(10)
          : undefined;
    if (value) out.push(value);
  });
  return out;
}

/** A Stryker command string as argv; anything shell-shaped goes through `sh -c`. */
export function commandArgv(command: string): string[] {
  const trimmed = command.trim();
  return SHELL_SYNTAX.test(trimmed) ? ["sh", "-c", trimmed] : trimmed.split(/\s+/);
}

function stringList(value: unknown): string[] {
  return Array.isArray(value) ? value.filter((v): v is string => typeof v === "string") : [];
}

function timeoutOf(raw: Record<string, unknown>): { factor: number; extraMs: number } | undefined {
  const factor = raw["timeoutFactor"];
  const ms = raw["timeoutMS"];
  if (typeof factor !== "number" && typeof ms !== "number") return undefined;
  // Stryker's defaults for the half that is missing.
  return {
    factor: typeof factor === "number" ? factor : 1.5,
    extraMs: typeof ms === "number" ? ms : 5000,
  };
}

function testsOf(raw: Record<string, unknown>, where: string): MutationTests {
  const bun = isRecord(raw["bun"]) ? raw["bun"] : {};
  const include = stringList(bun["testFiles"]);
  if (include.length === 0) throw new Error(`${where} has no bun.testFiles`);
  const preload = preloadArgs(stringList(bun["nodeArgs"]));
  return preload.length > 0 ? { include, preload } : { include };
}

/** `runner` or `tests`, by Stryker test runner. */
function runnerOf(raw: Record<string, unknown>, where: string): Record<string, unknown> {
  const runnerName = raw["testRunner"];
  if (runnerName === "command") {
    const cmd = isRecord(raw["commandRunner"]) ? raw["commandRunner"]["command"] : undefined;
    // Stryker's own default command.
    const argv = commandArgv(typeof cmd === "string" ? cmd : "npm test");
    return { runner: { kind: "command", argv } };
  }
  if (runnerName === undefined || runnerName === "bun") {
    return {
      tests: testsOf(raw, where),
      ...(raw["disableBail"] === true ? { mode: "matrix" } : {}),
    };
  }
  throw new Error(
    `${where}: testRunner "${String(runnerName)}" has no polly counterpart (bun or command)`
  );
}

function tuningOf(raw: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  if (typeof raw["concurrency"] === "number") out["concurrency"] = raw["concurrency"];
  const timeout = timeoutOf(raw);
  if (timeout) out["timeout"] = timeout;
  const excluded = isRecord(raw["mutator"]) ? stringList(raw["mutator"]["excludedMutations"]) : [];
  if (excluded.length > 0) out["mutators"] = { exclude: excluded };
  const brk = isRecord(raw["thresholds"]) ? raw["thresholds"]["break"] : undefined;
  if (typeof brk === "number") out["thresholds"] = { break: brk };
  return out;
}

/** Map a parsed Stryker config to a `MutationConfig`, with a note per dropped key. */
export function strykerToMutation(raw: unknown, where: string): Migration {
  if (!isRecord(raw)) throw new Error(`${where} is not a JSON object`);
  const draft = { targets: stringList(raw["mutate"]), ...runnerOf(raw, where), ...tuningOf(raw) };
  const notes: string[] = [];
  if (!stringList(raw["ignorers"]).includes("polly-verify")) {
    notes.push(
      "ignoreVerifyCallsites defaults to true: requires/ensures mutants are reported Ignored (polly#143)"
    );
  }
  const dropped = Object.keys(raw).filter((k) => !MAPPED.has(k) && !SILENT.has(k));
  if (dropped.length > 0) notes.push(`dropped Stryker-only keys: ${dropped.join(", ")}`);
  return { config: parseMutationConfig(draft, where), notes };
}

export async function readStrykerConfig(path: string): Promise<Migration> {
  return strykerToMutation(await Bun.file(path).json(), path);
}

/**
 * The specifier a config in `dir` imports `defineMutation` from: the package
 * export when it resolves there, else this source tree's own module (polly's
 * monorepo root has no `@fairfox/polly` in its node_modules).
 */
export function defineImportSpecifier(dir: string): string {
  try {
    Bun.resolveSync("@fairfox/polly/mutate", dir);
    return "@fairfox/polly/mutate";
  } catch {
    const local = join(import.meta.dir, "define.ts");
    if (!existsSync(local)) return "@fairfox/polly/mutate";
    const rel = relative(dir, local);
    return rel.startsWith(".") ? rel : `./${rel}`;
  }
}

/** Biome's default line width; a longer line is left one-element-per-line. */
const LINE_WIDTH = 100;

/**
 * Render a value as a TypeScript object literal in the shape biome's formatter
 * produces: unquoted keys, trailing commas, and an array of primitives on one
 * line when it fits in LINE_WIDTH, so `polly mutate init` passes `polly lint`.
 */
function literal(value: unknown): string {
  return JSON.stringify(value, null, 2)
    .replace(/^(\s*)"([A-Za-z_$][\w$]*)":/gm, "$1$2:")
    .replace(/([^\s[{,])(?=\n\s*[}\]])/g, "$1,")
    .replace(
      /^([ ]*)([\w$]+: )?\[\n((?:[ ]*(?:"[^"\n]*"|-?\d+(?:\.\d+)?|true|false),\n)+)([ ]*)\](,?)$/gm,
      (m, indent, key, items, _close, comma) => {
        const inline = `${indent}${key ?? ""}[${items
          .trim()
          .replace(/,$/, "")
          .split(/,\n\s*/)
          .join(", ")}]${comma}`;
        return inline.length <= LINE_WIDTH ? inline : m;
      }
    );
}

export function renderMutationConfig(config: MutationConfig, specifier: string): string {
  return [
    `import { defineMutation } from "${specifier}";`,
    "",
    `export default defineMutation(${literal(config)});`,
    "",
  ].join("\n");
}

export interface MigrateResult {
  /** Where the config goes (next to the Stryker config). */
  path: string;
  source: string;
  notes: string[];
  /** false when `write` was off or a config was already there without `force`. */
  written: boolean;
  existed: boolean;
}

export async function migrateConfig(
  strykerPath: string,
  opts: { write?: boolean; force?: boolean } = {}
): Promise<MigrateResult> {
  const { config, notes } = await readStrykerConfig(strykerPath);
  const dir = dirname(strykerPath);
  const path = join(dir, MUTATION_CONFIG_FILE);
  const source = renderMutationConfig(config, defineImportSpecifier(dir));
  const existed = existsSync(path);
  const written = Boolean(opts.write) && (!existed || Boolean(opts.force));
  if (written) await Bun.write(path, source);
  return { path, source, notes, written, existed };
}
