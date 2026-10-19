/**
 * Per-target result cache in `.polly/mutate/cache/` (one JSON file per key).
 *
 * The key is a sha256 over everything a target's results depend on:
 *   - the generated mutants (spans, replacements, operator names), which
 *     covers both the target's text and the operator rules
 *   - the text of every file in the covering tests' import closure, tests
 *     included
 *   - the project's preloads, tsconfig.json, bunfig.toml and bun.lock
 *   - mode, timeout, cwd isolation, Bun's version and CACHE_VERSION
 * Reach the import graph cannot see (a fixture file, `mock.module`) is not in
 * the key; `--no-cache` forces a fresh run.
 *
 * Only targets with a green baseline are stored. Results are matched back by
 * mutant content, not id, because ids carry the target's position in the run.
 */
import { existsSync, mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { Mutant, MutantResult, MutantStatus, TestRef } from "./types.ts";

/** Bump when the runner's semantics change in a way the key does not capture. */
export const CACHE_VERSION = 1;

export interface CachedResult {
  sig: string;
  status: MutantStatus;
  statusReason?: string;
  durationMs?: number;
  killedBy?: string[];
}

export interface CacheEntry {
  baselineMs: number;
  inTree: boolean;
  tests: TestRef[];
  results: CachedResult[];
}

export function mutantSig(
  m: Pick<Mutant, "start" | "end" | "replacement" | "mutatorName">
): string {
  return `${m.mutatorName}:${m.start}:${m.end}:${m.replacement}`;
}

async function textOrEmpty(path: string): Promise<string> {
  const file = Bun.file(path);
  return (await file.exists()) ? file.text() : "";
}

export async function cacheKey(input: {
  mutants: readonly Mutant[];
  closure: readonly string[];
  projectFiles: readonly string[];
  settings: unknown;
}): Promise<string> {
  const hash = new Bun.CryptoHasher("sha256");
  hash.update(JSON.stringify({ v: CACHE_VERSION, bun: Bun.version, settings: input.settings }));
  for (const m of input.mutants) hash.update(`${mutantSig(m)}|${m.ignoredReason ?? ""}\n`);
  for (const f of [...input.closure, ...input.projectFiles]) {
    hash.update(`\0${f}\0`);
    hash.update(await textOrEmpty(f));
  }
  return hash.digest("hex");
}

export async function readCache(dir: string, key: string): Promise<CacheEntry | null> {
  const file = Bun.file(join(dir, `${key}.json`));
  if (!(await file.exists())) return null;
  try {
    const entry: CacheEntry = await file.json();
    return Array.isArray(entry.results) ? entry : null;
  } catch {
    return null;
  }
}

export function writeCache(dir: string, key: string, entry: CacheEntry): void {
  mkdirSync(dir, { recursive: true });
  // The directory ignores itself, so a consumer's repo needs no .gitignore edit.
  const ignore = join(dir, ".gitignore");
  if (!existsSync(ignore)) writeFileSync(ignore, "*\n");
  writeFileSync(join(dir, `${key}.json`), `${JSON.stringify(entry)}\n`);
}

export function cachedResult(r: MutantResult): CachedResult {
  return {
    sig: mutantSig(r.mutant),
    status: r.status,
    ...(r.statusReason ? { statusReason: r.statusReason } : {}),
    ...(r.durationMs === undefined ? {} : { durationMs: r.durationMs }),
    ...(r.killedBy ? { killedBy: r.killedBy } : {}),
  };
}
