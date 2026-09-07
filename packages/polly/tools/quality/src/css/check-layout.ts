/**
 * CSS layout check.
 *
 * `display: flex` and `display: grid` are forbidden outside the Layout
 * primitive. Apps express layout through the `<Layout>` component so
 * layout decisions are declarative and greppable. There are two layout
 * primitives and the default exempt list is exactly those two: Layout owns
 * CSS grid, Cluster owns the one thing grid cannot do — a row of items that
 * keep their own widths and wrap. Everything else composes them. Consumers
 * can extend the list through `layoutExemptPaths`. Suppress one-off cases with a layout-ignore CSS
 * comment on the violating line or the line above.
 */

import type { CssCheckResult, CssViolation } from "./shared.ts";
import { makeResult, walkDirectory } from "./shared.ts";

export type CssLayoutOptions = {
  rootDir: string;
  /** File basenames or path fragments where layout CSS is permitted. */
  layoutExemptPaths?: string[];
  /** Directory names skipped during recursion. */
  skipDirs?: string[];
};

// `inline-flex` is matched too. It was not, and that blindness let polly-ui's
// own primitives go from 4 raw flex declarations to 16 in a single session
// without the count moving. `inline-grid` is deliberately absent: the only
// occurrence in the repo is Layout's own `inline` prop, in the exempt file.
const CSS_PATTERNS: Array<{ pattern: RegExp; kind: string }> = [
  { pattern: /display\s*:\s*inline-flex/, kind: "display: inline-flex in CSS" },
  { pattern: /display\s*:\s*flex/, kind: "display: flex in CSS" },
  { pattern: /display\s*:\s*grid/, kind: "display: grid in CSS" },
];

const TSX_PATTERNS: Array<{ pattern: RegExp; kind: string }> = [
  {
    pattern: /display\s*:\s*['"]inline-flex['"]/,
    kind: "display: inline-flex in inline style",
  },
  {
    pattern: /display\s*:\s*['"]flex['"]/,
    kind: "display: flex in inline style",
  },
  {
    pattern: /display\s*:\s*['"]grid['"]/,
    kind: "display: grid in inline style",
  },
];

const SUPPRESS = "layout-ignore";

export async function checkCssLayout(options: CssLayoutOptions): Promise<CssCheckResult> {
  const rootDir = options.rootDir;
  const exempt = options.layoutExemptPaths ?? [
    "Layout.module.css",
    "Layout.tsx",
    "Cluster.module.css",
    "Cluster.tsx",
  ];
  const violations: CssViolation[] = [];

  await walkDirectory(
    rootDir,
    // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: per-file visitor covers filetype, suppression, and pattern loop.
    async (full) => {
      const isCss = full.endsWith(".module.css");
      const isTsx = full.endsWith(".tsx");
      if (!isCss && !isTsx) return;
      if (exempt.some((fragment) => full.includes(fragment))) return;

      const patterns = isCss ? CSS_PATTERNS : TSX_PATTERNS;
      const content = await Bun.file(full).text();
      const lines = content.split("\n");

      for (let i = 0; i < lines.length; i += 1) {
        const line = lines[i];
        if (!line) continue;
        const trimmed = line.trim();
        if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*"))
          continue;
        if (trimmed.includes(SUPPRESS)) continue;
        const prev = i > 0 ? (lines[i - 1]?.trim() ?? "") : "";
        if (prev.includes(SUPPRESS)) continue;

        for (const rule of patterns) {
          if (rule.pattern.test(line)) {
            violations.push({
              file: full,
              line: i + 1,
              rule: rule.kind,
              content: trimmed,
              suggestion: "Use the <Layout> component instead",
            });
            break;
          }
        }
      }
    },
    {
      rootDir,
      skipDirs: options.skipDirs,
    }
  );

  return makeResult("css-layout", rootDir, violations);
}
