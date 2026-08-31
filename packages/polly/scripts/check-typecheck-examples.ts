#!/usr/bin/env bun

/**
 * Typecheck every example workspace.
 *
 * `bun run typecheck` covers packages/polly and its tests; `bun run
 * test:examples` runs three examples. Everything else under examples/ was
 * checked by nothing, so several rotted without a single red run: tsconfigs
 * naming a `bun-types` package that is not installed (tsc exited on TS2688 and
 * nobody read past it), a workspace with no tsconfig at all, undeclared
 * dependencies, and a preact pinned below polly's peer range so polly-ui
 * components could not be used as JSX.
 *
 * The examples are the documentation consumers copy, so a broken one is a
 * broken instruction. This check runs `tsc --noEmit` in each workspace that
 * has a tsconfig.json and reports every failure, not just the first.
 *
 *   bun scripts/check-typecheck-examples.ts [--verbose]
 */

import { existsSync } from "node:fs";
import { cpus } from "node:os";
import { dirname, join, relative } from "node:path";
import { Glob } from "bun";

/** The monorepo root — nearest ancestor of cwd (inclusive) holding the
 *  workspace manifest. packages/polly has an examples/ directory of its own
 *  (the e2e consumer fixture), so "has examples/" is not the marker. */
function repoRoot(): string {
  let dir = process.cwd();
  while (!existsSync(join(dir, "bun.lock"))) {
    const parent = dirname(dir);
    if (parent === dir) return process.cwd();
    dir = parent;
  }
  return dir;
}

const ROOT = repoRoot();
const VERBOSE = process.argv.includes("--verbose");

/** Every example workspace with its own tsconfig, in path order. */
async function exampleWorkspaces(): Promise<string[]> {
  const glob = new Glob("examples/**/tsconfig.json");
  const dirs: string[] = [];
  for await (const file of glob.scan({ cwd: ROOT, onlyFiles: true })) {
    if (file.includes("node_modules")) continue;
    dirs.push(join(ROOT, dirname(file)));
  }
  return dirs.sort();
}

interface Failure {
  workspace: string;
  output: string;
}

async function typecheck(dir: string): Promise<Failure | null> {
  const proc = Bun.spawn(["bunx", "tsc", "--noEmit"], {
    cwd: dir,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [out, err] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  const workspace = relative(ROOT, dir);
  if (proc.exitCode === 0) {
    if (VERBOSE) process.stdout.write(`  ✅ ${workspace}\n`);
    return null;
  }
  return { workspace, output: `${out}${err}`.trim() };
}

/** Drain the workspaces through a bounded pool — `tsc` is memory-hungry. */
async function run(): Promise<number> {
  const dirs = await exampleWorkspaces();
  if (dirs.length === 0) {
    process.stdout.write("✅ No example workspaces to typecheck\n");
    return 0;
  }

  const concurrency = Math.max(1, Math.min(4, cpus().length - 1));
  const failures: Failure[] = [];
  let next = 0;

  await Promise.all(
    Array.from({ length: Math.min(concurrency, dirs.length) }, async () => {
      while (next < dirs.length) {
        const dir = dirs[next++];
        if (!dir) return;
        const failure = await typecheck(dir);
        if (failure) failures.push(failure);
      }
    })
  );

  if (failures.length === 0) {
    process.stdout.write(`✅ Examples typecheck clean (${dirs.length} workspaces)\n`);
    return 0;
  }

  failures.sort((a, b) => a.workspace.localeCompare(b.workspace));
  process.stdout.write(`❌ ${failures.length} of ${dirs.length} example workspace(s) fail tsc:\n`);
  for (const failure of failures) {
    process.stdout.write(`\n  ${failure.workspace}\n`);
    for (const line of failure.output.split("\n").slice(0, 10)) {
      process.stdout.write(`    ${line}\n`);
    }
  }
  return 1;
}

process.exit(await run());
