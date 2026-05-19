#!/usr/bin/env bun

/**
 * Suppression-justification gate.
 *
 * Polly's lint and type configs already block most "look the other way"
 * shortcuts (noExplicitAny, noSkippedTests, noFocusedTests, noConsole,
 * noNonNullAssertion). The remaining escape hatches are the suppression
 * comments themselves: biome-ignore, ts-ignore, ts-expect-error,
 * eslint-disable. Each is a deliberate choice to downgrade a tool's
 * verdict on one line.
 *
 * Every new suppression must carry a tracking reference (matching #NNN,
 * polly#NNN, or issue-NNN) so the suppression has a path to deletion.
 * Existing untracked suppressions are grandfathered through
 * suppression-baseline.json: a snapshot of every suppression comment
 * that currently lives in the tree. To add a new suppression without a
 * ticket reference, the developer must explicitly extend the baseline,
 * which is itself reviewable.
 *
 * Usage:
 *   bun scripts/check-suppression-justifications.ts          # check
 *   bun scripts/check-suppression-justifications.ts --update # rewrite baseline
 */

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { Glob } from "bun";

const ROOT = process.cwd();
const BASELINE_PATH = resolve(ROOT, "suppression-baseline.json");

const SCAN_DIRS = ["src", "tools", "tests", "scripts", "cli"];
const SCAN_EXTS = ["ts", "tsx", "js", "jsx"];

// Match real suppression directives. A directive is recognised when it
// appears at the start of a line comment (// ...), a block-comment line
// (/* ... or  *  ...), or as an inline trailing comment (` // ... `).
// JSDoc descriptive prose that quotes one of the keywords (e.g.
// "the ignore directive...") and help text that mentions the keywords
// do not count.
const SUPPRESSION_PATTERN =
  /(?:^|\s)\/\/\s*(?:biome-ignore|@ts-ignore|@ts-expect-error|eslint-disable)\b|^\s*\/?\*+\s*(?:biome-ignore|@ts-ignore|@ts-expect-error|eslint-disable)\b/;

// Acceptable ticket-reference shapes: #NNN, polly#NNN, issue-NNN.
const TICKET_PATTERN = /(?:polly)?#\d+|issue-\d+/;

interface Suppression {
  /** Path relative to ROOT. */
  file: string;
  /** Verbatim line content (trimmed). */
  text: string;
}

interface BaselineEntry {
  file: string;
  text: string;
}

async function collectSuppressions(): Promise<Suppression[]> {
  const out: Suppression[] = [];
  for (const dir of SCAN_DIRS) {
    const root = resolve(ROOT, dir);
    if (!existsSync(root)) continue;
    const glob = new Glob(`**/*.{${SCAN_EXTS.join(",")}}`);
    for await (const absPath of glob.scan({ cwd: root, absolute: true })) {
      const contents = readFileSync(absPath, "utf-8");
      const rel = absPath.replace(`${ROOT}/`, "");
      for (const line of contents.split("\n")) {
        if (SUPPRESSION_PATTERN.test(line)) {
          out.push({ file: rel, text: line.trim() });
        }
      }
    }
  }
  out.sort((a, b) =>
    a.file === b.file ? a.text.localeCompare(b.text) : a.file.localeCompare(b.file)
  );
  return out;
}

function loadBaseline(): BaselineEntry[] {
  if (!existsSync(BASELINE_PATH)) return [];
  try {
    const raw = JSON.parse(readFileSync(BASELINE_PATH, "utf-8")) as unknown;
    if (!Array.isArray(raw)) return [];
    return raw.filter(
      (entry): entry is BaselineEntry =>
        typeof entry === "object" &&
        entry !== null &&
        typeof (entry as Record<string, unknown>)["file"] === "string" &&
        typeof (entry as Record<string, unknown>)["text"] === "string"
    );
  } catch {
    return [];
  }
}

function keyOf(s: { file: string; text: string }): string {
  return `${s.file}::${s.text}`;
}

const update = process.argv.includes("--update");

const current = await collectSuppressions();

if (update) {
  writeFileSync(BASELINE_PATH, `${JSON.stringify(current, null, 2)}\n`);
  process.stdout.write(`✅ Wrote ${current.length} suppression(s) to suppression-baseline.json\n`);
  process.exit(0);
}

const baseline = loadBaseline();
const baselineKeys = new Set(baseline.map(keyOf));

const introduced = current.filter((s) => !baselineKeys.has(keyOf(s)));
const unjustified = introduced.filter((s) => !TICKET_PATTERN.test(s.text));

if (unjustified.length > 0) {
  process.stderr.write(`❌ ${unjustified.length} new suppression(s) without a ticket reference:\n`);
  for (const s of unjustified) {
    process.stderr.write(`   ${s.file}\n     ${s.text}\n`);
  }
  process.stderr.write(
    "\n   Add a #NNN, polly#NNN, or issue-NNN to the suppression comment, or\n" +
      "   regenerate the baseline with `bun scripts/check-suppression-justifications.ts --update`\n" +
      "   (only when you genuinely intend to grandfather this suppression in).\n"
  );
  process.exit(1);
}

const justifiedNew = introduced.length - unjustified.length;
process.stdout.write(
  `✅ Suppression gate clean (${current.length} total, ${baseline.length} baseline, ${justifiedNew} new with ticket)\n`
);
process.exit(0);
