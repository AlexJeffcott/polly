/**
 * Content-hash cache for the quality plugin host.
 *
 * Each check declares the files and extras that determine its result.
 * The cache hashes those into a key, looks up `.cache/polly-quality/<id>.json`,
 * and returns the prior result on hit. A miss re-runs the check body and
 * writes a fresh entry.
 *
 * Files that are missing on disk hash as the literal string `<absent>`
 * so removing a declared input invalidates the entry deterministically.
 * Atomic writes go through a temp file + rename so a process crashing
 * mid-write cannot leave a partial JSON behind that later parses to a
 * malformed entry. A corrupt entry is treated as a miss with a warning;
 * the check re-runs and overwrites it.
 */

import { createHash } from "node:crypto";
import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import { dirname, isAbsolute, join, resolve } from "node:path";
import type { CheckOutcome } from "./types";

export type CacheInputs = {
  files: string[];
  extras?: Record<string, string>;
};

export type CacheEntry = {
  hash: string;
  outcome: CheckOutcome;
  /** Wall-clock time the entry was written; useful for debugging stale caches. */
  writtenAt: string;
};

const ABSENT_MARKER = "<absent>";

async function hashFile(path: string): Promise<string> {
  try {
    const buf = await readFile(path);
    const h = createHash("sha256");
    h.update(buf);
    return h.digest("hex");
  } catch {
    return ABSENT_MARKER;
  }
}

/**
 * Compute a deterministic SHA-256 over (sorted file paths + content hashes
 * + sorted extras). Identical inputs in any order produce the same hash;
 * adding, removing, renaming, or modifying any input changes it.
 */
export async function computeInputsHash(inputs: CacheInputs, rootDir: string): Promise<string> {
  const filePairs: Array<{ path: string; hash: string }> = [];
  for (const f of inputs.files) {
    const abs = isAbsolute(f) ? f : resolve(rootDir, f);
    const hash = await hashFile(abs);
    // Store the relative-to-root form so caches survive a checkout move.
    const rel = abs.startsWith(`${rootDir}/`) ? abs.slice(rootDir.length + 1) : abs;
    filePairs.push({ path: rel, hash });
  }
  filePairs.sort((a, b) => a.path.localeCompare(b.path));

  const extras = inputs.extras ?? {};
  const extrasPairs = Object.keys(extras)
    .sort()
    .map((k) => ({ key: k, value: extras[k] ?? "" }));

  const payload = JSON.stringify({ files: filePairs, extras: extrasPairs });
  return createHash("sha256").update(payload).digest("hex");
}

function cachePath(rootDir: string, checkId: string): string {
  // Replace `:` with `__` so `polly:no-as-casting` becomes a valid filename
  // on every platform.
  const safe = checkId.replace(/:/g, "__");
  return join(rootDir, ".cache", "polly-quality", `${safe}.json`);
}

export async function getCachedOutcome(
  rootDir: string,
  checkId: string,
  hash: string
): Promise<CheckOutcome | null> {
  const path = cachePath(rootDir, checkId);
  let raw: string;
  try {
    raw = await readFile(path, "utf8");
  } catch {
    return null;
  }
  let parsed: CacheEntry;
  try {
    parsed = JSON.parse(raw) as unknown as CacheEntry;
  } catch {
    // Treat corrupt entries as misses; the check will re-run and the next
    // write replaces the bad file. We deliberately don't throw — a busted
    // cache should not block a CI run.
    return null;
  }
  if (parsed.hash !== hash) return null;
  if (typeof parsed.outcome?.ok !== "boolean" || !Array.isArray(parsed.outcome?.messages)) {
    return null;
  }
  return parsed.outcome;
}

export async function setCachedOutcome(
  rootDir: string,
  checkId: string,
  hash: string,
  outcome: CheckOutcome
): Promise<void> {
  const path = cachePath(rootDir, checkId);
  await mkdir(dirname(path), { recursive: true });
  const entry: CacheEntry = { hash, outcome, writtenAt: new Date().toISOString() };
  const tmp = `${path}.tmp-${process.pid}-${Date.now()}`;
  await writeFile(tmp, JSON.stringify(entry, null, 2));
  await rename(tmp, path);
}
