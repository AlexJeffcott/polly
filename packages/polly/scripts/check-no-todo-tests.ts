#!/usr/bin/env bun

/**
 * Bans `it.todo`, `test.todo`, `it.failing`, `test.failing` in tests/**.
 *
 * Biome's `noSkippedTests` covers `.skip` and `noFocusedTests` covers
 * `.only`. The `.todo` and `.failing` forms are not covered by either
 * because Biome treats them as legitimate test-runner features, but
 * they corrode the "green CI = correct" signal:
 *
 *   - `.todo` looks like coverage but is a no-op. A reader scanning a
 *     test file sees "test X" and assumes X is asserted; it isn't.
 *
 *   - `.failing` flips the polarity: a test that begins to pass after
 *     it was marked failing silently turns into a failure under most
 *     runners. The semantic ambiguity is its own bug class.
 *
 * Replace either with a tracked issue. If a test is intentionally
 * disabled because the work is queued, the issue is the source of
 * truth; not a string in a file that gets forgotten.
 */

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { Glob } from "bun";

const ROOT = process.cwd();
const TESTS_DIR = resolve(ROOT, "tests");

// Matches it.todo, test.todo, describe.todo, it.failing, test.failing.
// Word boundary at the front prevents `units.todo` and similar from
// false-matching. The `\b` after handles `.todo(` and `.todo  (`.
const PATTERN = /\b(?:it|test|describe)\.(?:todo|failing)\b/;

interface Hit {
  file: string;
  line: number;
  text: string;
}

async function findHits(): Promise<Hit[]> {
  const hits: Hit[] = [];
  const glob = new Glob("**/*.{ts,tsx,js,jsx}");
  for await (const file of glob.scan({ cwd: TESTS_DIR, absolute: true })) {
    const contents = readFileSync(file, "utf-8");
    const lines = contents.split("\n");
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (line === undefined) continue;
      if (PATTERN.test(line)) {
        hits.push({ file: file.replace(`${ROOT}/`, ""), line: i + 1, text: line.trim() });
      }
    }
  }
  return hits;
}

const hits = await findHits();
if (hits.length === 0) {
  process.stdout.write("✅ No .todo / .failing tests under tests/\n");
  process.exit(0);
}

process.stderr.write(`❌ Found ${hits.length} .todo / .failing test usage(s) under tests/:\n`);
for (const hit of hits) {
  process.stderr.write(`   ${hit.file}:${hit.line}\n     ${hit.text}\n`);
}
process.stderr.write(
  "\n   Replace with a tracked issue. .todo looks like coverage but is a no-op;\n" +
    "   .failing flips polarity and silently turns into a failure when the test\n" +
    "   starts passing.\n"
);
process.exit(1);
