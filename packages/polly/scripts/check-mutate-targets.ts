#!/usr/bin/env bun

/**
 * Validates that every `mutate` path in stryker.conf.json still exists on disk
 * (and that each `bun.testFiles` glob still matches at least one file).
 *
 * Stryker's mutate list is a hand-curated set of paths — the modules the kill
 * matrix actually scores. When one of those files is renamed or moved, nothing
 * fails: Stryker just mutates fewer files, and the only thing that would
 * surface the gap is a ~45-minute mutation run whose number quietly drops.
 * That is the same silent-rot failure the unit-coverage orphan detector
 * guards against, one layer down — a curated list that lies because no cheap
 * check holds it to the tree.
 *
 * This runs in milliseconds, so a rotted mutate path is caught at gate time
 * instead of being discovered (or missed) during the next mutation pass.
 */

import { existsSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { Glob } from "bun";

const ROOT = process.cwd();

/** Nearest ancestor of cwd (inclusive) holding stryker.conf.json. The config
 *  lives at the monorepo root, above this package since the packages/ split. */
function findStrykerConfig(): string | null {
  let dir = ROOT;
  while (!existsSync(join(dir, "stryker.conf.json"))) {
    const parent = dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
  return join(dir, "stryker.conf.json");
}

interface StrykerConfig {
  mutate?: string[];
  bun?: { testFiles?: string[] };
}

function isGlob(pattern: string): boolean {
  return pattern.includes("*") || pattern.includes("?") || pattern.includes("[");
}

async function globMatchesAny(pattern: string, cwd: string): Promise<boolean> {
  const glob = new Glob(pattern);
  for await (const _ of glob.scan({ cwd, onlyFiles: true })) return true;
  return false;
}

/** Returns the entries that resolve to nothing — a missing file, or a glob
 *  that matches no file. */
async function findMissing(entries: string[], configDir: string): Promise<string[]> {
  const missing: string[] = [];
  for (const entry of entries) {
    const present = isGlob(entry)
      ? await globMatchesAny(entry, configDir)
      : existsSync(resolve(configDir, entry));
    if (!present) missing.push(entry);
  }
  return missing;
}

const configPath = findStrykerConfig();
if (configPath === null) {
  process.stdout.write("⏩ No stryker.conf.json found — skipping mutate-target check\n");
  process.exit(0);
}

const configDir = dirname(configPath);
const config = JSON.parse(readFileSync(configPath, "utf8")) as StrykerConfig;
const mutate = config.mutate ?? [];
const testFiles = config.bun?.testFiles ?? [];

const missingMutate = await findMissing(mutate, configDir);
const emptyTestGlobs = await findMissing(testFiles, configDir);

if (missingMutate.length === 0 && emptyTestGlobs.length === 0) {
  process.stdout.write(
    `✅ All ${mutate.length} stryker mutate targets exist (${testFiles.length} testFiles globs match)\n`
  );
  process.exit(0);
}

if (missingMutate.length > 0) {
  process.stderr.write(`❌ ${missingMutate.length} stryker mutate target(s) no longer exist:\n`);
  for (const p of missingMutate) process.stderr.write(`   ${p}\n`);
  process.stderr.write("   A renamed/deleted file silently drops out of the mutation matrix.\n");
  process.stderr.write("   Fix the path in stryker.conf.json, or remove the entry.\n");
}

if (emptyTestGlobs.length > 0) {
  process.stderr.write(`❌ ${emptyTestGlobs.length} stryker testFiles glob(s) match no files:\n`);
  for (const p of emptyTestGlobs) process.stderr.write(`   ${p}\n`);
}

process.exit(1);
