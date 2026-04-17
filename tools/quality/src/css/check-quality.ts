/**
 * CSS quality check.
 *
 * Every styled value that has a semantic token must reference the token.
 * Raw hex colours, rgba literals, rem values, numeric font-weights,
 * magic z-indexes, hardcoded border-radius / border-width / box-shadow,
 * inline transitions, and `!important` are all rejected. The rule set
 * is intentionally opinionated; consumers who need an escape hatch may
 * place a polly-ignore-all marker in a CSS comment on the first line
 * of a file to skip checks for that file.
 */

import { makeResult, walkDirectory, isInsideComment, isInsideKeyframes } from "./shared.ts";
import type { CssCheckResult, CssViolation } from "./shared.ts";

export type CssQualityOptions = {
  rootDir: string;
  /** Scan filter — files whose basename ends with one of these are checked. Default: `.module.css`. */
  extensions?: string[];
  /** File basenames skipped entirely. Default: `["theme.css", "tokens.css"]`. */
  skipFiles?: string[];
  /** Directory names skipped during recursion. */
  skipDirs?: string[];
  /** Which rules to disable by id. */
  disableRules?: string[];
};

type Rule = {
  id: string;
  check: (
    line: string,
    lineNum: number,
    allLines: readonly string[],
  ) => string | null;
};

const DEFAULT_RULES: Rule[] = [
  {
    id: "no-hardcoded-color",
    check: (line) => {
      if (isInsideComment(line)) return null;
      if (line.includes("var(")) return null;
      if (/\bcolor:\s*(white|black|#[0-9a-fA-F]{3,8})\b/.test(line)) {
        return "Use a semantic colour token (--polly-text, --polly-text-muted, …)";
      }
      if (
        /background(-color)?:\s*#[0-9a-fA-F]{3,8}/.test(line) &&
        !line.includes("var(")
      ) {
        return "Use a semantic surface token (--polly-surface, --polly-surface-raised, …)";
      }
      return null;
    },
  },
  {
    id: "no-hardcoded-rgba",
    check: (line) => {
      if (isInsideComment(line)) return null;
      if (!line.includes("rgba(")) return null;
      if (line.includes("var(")) return null;
      if (line.includes("color-mix(")) return null;
      if (/background.*rgba/.test(line)) {
        return "Use a semantic surface or overlay token";
      }
      if (/box-shadow.*rgba/.test(line)) {
        return "Use a semantic shadow token";
      }
      return "Use a semantic token instead of raw rgba()";
    },
  },
  {
    id: "no-hardcoded-z-index",
    check: (line) => {
      const m = line.match(/z-index:\s*(\d+)/);
      if (!m?.[1]) return null;
      if (line.includes("var(")) return null;
      if (Number.parseInt(m[1], 10) < 10) return null;
      return "Use a --polly-z-* token";
    },
  },
  {
    id: "no-hardcoded-opacity",
    check: (line) => {
      if (!/opacity:\s*0\.\d/.test(line)) return null;
      if (line.includes("var(")) return null;
      const m = line.match(/opacity:\s*(0\.\d+)/);
      if (!m?.[1]) return null;
      const v = Number.parseFloat(m[1]);
      if (v >= 0.5 && v <= 0.7) {
        return "Use var(--polly-opacity-disabled) for disabled states";
      }
      return null;
    },
  },
  {
    id: "no-hardcoded-transition",
    check: (line, lineNum, allLines) => {
      if (isInsideKeyframes(lineNum, allLines)) return null;
      if (line.includes("var(--polly-motion")) return null;
      if (!/(?:transition|animation)/.test(line)) return null;
      if (
        /\d+(\.\d+)?(ms|s)\s+(ease|linear|ease-in|ease-out|ease-in-out)/.test(
          line,
        ) &&
        !line.includes("infinite")
      ) {
        return "Use var(--polly-motion-fast|base|slow)";
      }
      if (/\s\d+(\.\d+)?s[;\s,]/.test(line) && !line.includes("infinite")) {
        return "Use var(--polly-motion-fast|base|slow)";
      }
      return null;
    },
  },
  {
    id: "no-important",
    check: (line) => {
      if (isInsideComment(line)) return null;
      if (!line.includes("!important")) return null;
      return "Refactor specificity instead of using !important";
    },
  },
  {
    id: "no-rem-units",
    check: (line, lineNum, allLines) => {
      if (isInsideComment(line)) return null;
      if (isInsideKeyframes(lineNum, allLines)) return null;
      if (/:\s*[^;]*\d+(\.\d+)?rem[;\s]/.test(line)) {
        if (line.includes("calc(") || line.includes("translateY(")) {
          return null;
        }
        return "Use --polly-space-* or --polly-text-* tokens instead of rem";
      }
      return null;
    },
  },
  {
    id: "no-hardcoded-border-width",
    check: (line) => {
      if (isInsideComment(line)) return null;
      if (line.includes("var(--polly-border-width")) return null;
      const m = line.match(
        /border(?:-(?:top|right|bottom|left))?:\s*(\d+)px\s+solid/,
      );
      if (!m?.[1]) return null;
      return "Use a --polly-border-width-* token";
    },
  },
  {
    id: "no-hardcoded-border-radius",
    check: (line) => {
      if (isInsideComment(line)) return null;
      if (line.includes("var(")) return null;
      const m = line.match(/border-radius:\s*(\d+)px/);
      if (!m?.[1]) return null;
      if (m[1] === "0") return null;
      return "Use a --polly-radius-{sm,md,lg} token";
    },
  },
  {
    id: "no-hardcoded-box-shadow",
    check: (line) => {
      if (isInsideComment(line)) return null;
      if (!line.includes("box-shadow:")) return null;
      if (line.includes("var(--polly-shadow")) return null;
      if (line.includes("var(--polly-focus-ring")) return null;
      if (line.includes("var(")) return null;
      if (/box-shadow:\s*none/.test(line)) return null;
      return "Use var(--polly-shadow-*) or var(--polly-focus-ring)";
    },
  },
  {
    id: "no-hardcoded-font-weight",
    check: (line) => {
      if (!/font-weight:\s*\d{3}/.test(line)) return null;
      if (line.includes("var(")) return null;
      return "Use var(--polly-weight-normal|medium|bold)";
    },
  },
];

export async function checkCssQuality(
  options: CssQualityOptions,
): Promise<CssCheckResult> {
  const rootDir = options.rootDir;
  const extensions = options.extensions ?? [".module.css"];
  const skipFiles = options.skipFiles ?? ["theme.css", "tokens.css"];
  const disabled = new Set(options.disableRules ?? []);
  const rules = DEFAULT_RULES.filter((r) => !disabled.has(r.id));
  const violations: CssViolation[] = [];

  await walkDirectory(
    rootDir,
    async (full) => {
      if (!extensions.some((ext) => full.endsWith(ext))) return;
      const content = await Bun.file(full).text();
      const lines = content.split("\n");
      const hasFileIgnore = lines[0]?.includes("polly-ignore-all");
      if (hasFileIgnore) return;

      for (let i = 0; i < lines.length; i += 1) {
        const line = lines[i];
        if (!line) continue;
        const trimmed = line.trim();
        if (trimmed === "" || trimmed === "{" || trimmed === "}") continue;
        for (const rule of rules) {
          const suggestion = rule.check(line, i, lines);
          if (suggestion) {
            violations.push({
              file: full,
              line: i + 1,
              rule: rule.id,
              content: trimmed,
              suggestion,
            });
          }
        }
      }
    },
    {
      rootDir,
      skipDirs: options.skipDirs,
      skipFiles,
    },
  );

  return makeResult("css-quality", rootDir, violations);
}
