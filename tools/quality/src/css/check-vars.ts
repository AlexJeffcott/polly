/**
 * CSS variable reference validator.
 *
 * Two-pass scanner. First pass collects every `--name:` definition in
 * every `.css` file under the root. Second pass walks `.css`, `.ts`, and
 * `.tsx` files and reports any `var(--name)` that does not resolve. Catches
 * typos, stale references, and references to removed tokens.
 *
 * Variables that are set via JS (inline style) can be declared via
 * `dynamicVars` so they are treated as defined without appearing in CSS.
 */

import { makeResult, walkDirectory } from "./shared.ts";
import type { CssCheckResult, CssViolation } from "./shared.ts";

export type CssVarsOptions = {
  rootDir: string;
  /** Extensions scanned for var(--x) references. Default: css, ts, tsx. */
  scanExtensions?: string[];
  /** Variables defined dynamically (set via JS). Treated as defined. */
  dynamicVars?: string[];
  /** Directory names skipped during recursion. */
  skipDirs?: string[];
};

export async function checkCssVars(
  options: CssVarsOptions,
): Promise<CssCheckResult> {
  const rootDir = options.rootDir;
  const scanExts = options.scanExtensions ?? [".ts", ".tsx", ".css"];
  const dynamic = new Set(options.dynamicVars ?? []);
  const definitions = new Set<string>(dynamic);
  const violations: CssViolation[] = [];

  // Pass 1 — collect all CSS custom property definitions
  await walkDirectory(
    rootDir,
    async (full) => {
      if (!full.endsWith(".css")) return;
      const content = await Bun.file(full).text();
      for (const m of content.matchAll(/--([\w-]+)\s*:/g)) {
        if (m[1]) definitions.add(`--${m[1]}`);
      }
    },
    { rootDir, skipDirs: options.skipDirs },
  );

  // Pass 2 — scan var(--name) references
  await walkDirectory(
    rootDir,
    async (full) => {
      if (full.endsWith(".css.d.ts")) return;
      if (!scanExts.some((ext) => full.endsWith(ext))) return;
      const content = await Bun.file(full).text();
      const lines = content.split("\n");
      for (let i = 0; i < lines.length; i += 1) {
        const line = lines[i];
        if (!line) continue;
        for (const m of line.matchAll(/var\(--([\w-]+)\)/g)) {
          const name = `--${m[1]}`;
          if (!definitions.has(name)) {
            violations.push({
              file: full,
              line: i + 1,
              rule: "undefined-var",
              content: line.trim(),
              suggestion: `Define ${name} in a CSS file or add to dynamicVars`,
            });
          }
        }
      }
    },
    { rootDir, skipDirs: options.skipDirs },
  );

  return makeResult("css-vars", rootDir, violations);
}
