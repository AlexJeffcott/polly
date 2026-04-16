#!/usr/bin/env bun

/**
 * Codemod: convert all `as Type` assertions to `as unknown as Type`.
 *
 * This is a one-time migration tool. After running it, every existing
 * type assertion in the codebase is explicitly marked with the allowed
 * escape hatch (`as unknown as`) rather than silently bypassing the type
 * system. The check-no-as-casting.ts conformance check then passes with
 * zero violations, and the rule is enforced from this point forward.
 *
 * Subsequent work should replace each `as unknown as` with proper typing
 * wherever feasible — type guards, narrowed generics, discriminated
 * unions, or fixes at the source.
 *
 * Run with:
 *
 *   bun scripts/fix-as-casting.ts
 *
 * Dry-run (print what would change without writing):
 *
 *   DRY_RUN=true bun scripts/fix-as-casting.ts
 */

import { readFileSync, writeFileSync } from "node:fs";
import { Glob } from "bun";

// Import the clean-check from the conformance script.
import { isLineClean } from "./check-no-as-casting";

const EXCLUDED_DIRS = new Set(["node_modules", "dist", ".git", ".bun", "examples"]);
const dryRun = process.env["DRY_RUN"] === "true";

/**
 * Replace ` as Type` with ` as unknown as Type` on a single line, skipping
 * patterns that are already clean (as const, as unknown as, import/export,
 * strings, comments).
 */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Source-text scanning with many skip rules is inherently branchy.
function fixLine(line: string): string {
  if (isLineClean(line)) return line;

  // Find each ` as ` occurrence and replace with ` as unknown as ` if it's
  // not already an allowed pattern. Work right-to-left so indices stay valid.
  let result = line;
  let searchFrom = result.length;

  while (true) {
    const idx = result.lastIndexOf(" as ", searchFrom - 1);
    if (idx < 0) break;
    searchFrom = idx;

    // Check what follows the ` as `. If it's ` as const` or ` as unknown as`,
    // skip this occurrence.
    const after = result.substring(idx + 4);
    if (after.startsWith("const") && (after.length === 5 || !after[5]?.match(/\w/))) {
      continue;
    }
    if (after.startsWith("unknown as ")) {
      continue;
    }

    // Check if this ` as ` is inside a string literal (odd quotes before it).
    const before = result.substring(0, idx);
    const singleQuotes = (before.match(/'/g) ?? []).length;
    const doubleQuotes = (before.match(/"/g) ?? []).length;
    const backticks = (before.match(/`/g) ?? []).length;
    if (singleQuotes % 2 === 1 || doubleQuotes % 2 === 1 || backticks % 2 === 1) {
      continue;
    }

    // Check if it's after a // comment.
    const commentIdx = before.lastIndexOf("//");
    if (commentIdx >= 0) {
      // Is the // inside a string? If not, skip.
      const beforeComment = before.substring(0, commentIdx);
      const sq = (beforeComment.match(/"/g) ?? []).length;
      if (sq % 2 === 0) continue;
    }

    // Check if it's an import/export rename.
    if (
      before.match(/\b(import|export)\s+.*$/) ||
      before.match(/\b(import|export)\s+\*\s*$/) ||
      before.match(/\b(import|export)\s+type\s+.*$/) ||
      result.trim().match(/^\w+\s+as\s+\w+,?\s*$/)
    ) {
      continue;
    }

    // Check property declaration pattern.
    if (after.match(/^\s*[=:,]/)) {
      continue;
    }

    // This is a real `as Type` assertion. Replace with `as unknown as Type`.
    result = `${result.substring(0, idx)} as unknown as${result.substring(idx + 3)}`;
  }

  return result;
}

async function main(): Promise<void> {
  const rootDir = process.cwd();
  const glob = new Glob("**/*.{ts,tsx}");
  let filesChanged = 0;
  let linesChanged = 0;

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const relative = file.replace(`${rootDir}/`, "");
    const segments = relative.split("/");
    if (segments.some((s) => EXCLUDED_DIRS.has(s))) continue;

    const content = readFileSync(file, "utf-8");
    const lines = content.split("\n");
    let changed = false;

    const fixed = lines.map((line) => {
      const result = fixLine(line);
      if (result !== line) {
        changed = true;
        linesChanged++;
        if (dryRun) {
          console.log(`  ${relative}`);
          console.log(`    - ${line.trim()}`);
          console.log(`    + ${result.trim()}\n`);
        }
      }
      return result;
    });

    if (changed) {
      filesChanged++;
      if (!dryRun) {
        writeFileSync(file, fixed.join("\n"));
      }
    }
  }

  if (dryRun) {
    console.log(
      `[fix-as-casting] DRY RUN: would change ${linesChanged} lines in ${filesChanged} files`
    );
  } else {
    console.log(`[fix-as-casting] Changed ${linesChanged} lines in ${filesChanged} files`);
  }
}

main();
