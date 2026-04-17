/**
 * Unused CSS detection (advisory).
 *
 * Finds classes and locally-defined custom properties in `.module.css`
 * files that appear to have no reference. Classes are checked against
 * every `.ts` / `.tsx` file's textual content; variables are checked
 * against other CSS files plus JS/TS referencing the same `--name`.
 * Matching is string-based and cannot see through dynamic lookups —
 * so this check is advisory only. Violations are returned as warnings;
 * the caller decides whether to fail the build.
 */

import type { CssCheckResult, CssViolation } from "./shared.ts";
import { makeResult, walkDirectory } from "./shared.ts";

export type CssUnusedOptions = {
  rootDir: string;
  /** Directory names skipped during recursion. */
  skipDirs?: string[];
  /** Class names treated as always-used (e.g. framework-generated). */
  alwaysUsedClasses?: string[];
};

type Definition = {
  file: string;
  name: string;
  line: number;
  type: "class" | "variable";
};

export async function checkCssUnused(options: CssUnusedOptions): Promise<CssCheckResult> {
  const rootDir = options.rootDir;
  const alwaysUsed = new Set(options.alwaysUsedClasses ?? []);
  const definitions: Definition[] = [];
  const tsContents: Array<{ file: string; content: string }> = [];
  const cssContents: Array<{ file: string; content: string }> = [];

  await walkDirectory(
    rootDir,
    // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: filetype dispatch with nested matchAll scans; flat branches.
    async (full) => {
      if (full.endsWith(".module.css")) {
        const content = await Bun.file(full).text();
        const lines = content.split("\n");
        for (let i = 0; i < lines.length; i += 1) {
          const line = lines[i];
          if (!line) continue;
          for (const m of line.matchAll(/(?:^|[\s,>+~])\.([\w-]+)/g)) {
            if (m[1]) {
              definitions.push({
                file: full,
                name: m[1],
                line: i + 1,
                type: "class",
              });
            }
          }
          for (const m of line.matchAll(/^\s+--([\w-]+)\s*:/g)) {
            if (m[1]) {
              definitions.push({
                file: full,
                name: `--${m[1]}`,
                line: i + 1,
                type: "variable",
              });
            }
          }
        }
        cssContents.push({ file: full, content });
      } else if (full.endsWith(".css") && !full.endsWith(".css.d.ts")) {
        const content = await Bun.file(full).text();
        cssContents.push({ file: full, content });
      } else if ((full.endsWith(".ts") || full.endsWith(".tsx")) && !full.endsWith(".css.d.ts")) {
        const content = await Bun.file(full).text();
        tsContents.push({ file: full, content });
      }
    },
    { rootDir, skipDirs: options.skipDirs }
  );

  // Deduplicate definitions (same class may appear in multiple selectors)
  const seen = new Set<string>();
  const uniqueDefs = definitions.filter((d) => {
    const key = `${d.file}:${d.type}:${d.name}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });

  function classReferenced(name: string): boolean {
    if (alwaysUsed.has(name)) return true;
    for (const { content } of tsContents) {
      if (
        content.includes(`.${name}`) ||
        content.includes(`['${name}']`) ||
        content.includes(`["${name}"]`)
      ) {
        return true;
      }
    }
    return false;
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: three-way reference check (other CSS, same CSS self-count, TS references).
  function variableReferenced(name: string, defFile: string): boolean {
    for (const { file, content } of cssContents) {
      if (file === defFile) continue;
      if (content.includes(`var(${name})`)) return true;
    }
    const self = cssContents.find((f) => f.file === defFile);
    if (self) {
      const occurrences = self.content.split(name).length - 1;
      if (occurrences > 1) return true;
    }
    for (const { content } of tsContents) {
      if (content.includes(name)) return true;
    }
    return false;
  }

  const violations: CssViolation[] = [];
  for (const def of uniqueDefs) {
    if (def.type === "class" && !classReferenced(def.name)) {
      violations.push({
        file: def.file,
        line: def.line,
        rule: "unused-class",
        content: `.${def.name}`,
        suggestion: "Delete the selector or reference the class from a component",
      });
    } else if (def.type === "variable" && !variableReferenced(def.name, def.file)) {
      violations.push({
        file: def.file,
        line: def.line,
        rule: "unused-variable",
        content: def.name,
        suggestion: "Delete the definition or reference the variable",
      });
    }
  }

  return makeResult("css-unused (advisory)", rootDir, violations);
}
