/**
 * Ban raw native interactive HTML elements in app source.
 *
 * Applications that consume `@fairfox/polly/ui` are expected to use
 * the shared primitives (`<Button>`, `<ActionInput>`, `<Layout>`,
 * `<Modal>`, `<ActionForm>`, `<Select>`) rather than writing raw
 * `<button>`, `<input>`, `<select>`, `<textarea>`, `<form>`, or
 * `<dialog>` elements. The primitives enforce data-action delegation,
 * typed CSS-module classNames, accessibility attributes, and the
 * layouting ban.
 *
 * This module exposes a programmatic check — `checkSharedComponents`
 * — that walks a directory, scans every .tsx / .jsx file, and
 * returns every violation it finds. Consumers typically wire it into
 * a `bun check` script and set `exemptPackages` / `allowPaths` for
 * legacy code that can't migrate yet.
 *
 * @example
 * ```ts
 * import { checkSharedComponents } from "@fairfox/polly/quality";
 *
 * const result = await checkSharedComponents({
 *   root: process.cwd(),
 *   scanRoot: "packages",
 *   exemptPackages: new Set(["struggle", "todo"]),
 * });
 * if (result.violations.length > 0) {
 *   result.print(console.error);
 *   process.exit(1);
 * }
 * ```
 */

import type { Dirent } from "node:fs";
import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";

/** One raw-element rule. Each rule flags a native element and
 * suggests the polly primitive that replaces it. */
export interface SharedComponentRule {
  /** Regular expression that matches the opening tag, e.g. /<button[\s>]/. */
  pattern: RegExp;
  /** Human-readable element marker, e.g. "<button>". */
  element: string;
  /** Suggested replacement, e.g. "<Button>". */
  replacement: string;
  /** Optional predicate; when it returns true the match is skipped.
   * Used for legitimate raw usages (e.g. `<input type="hidden">`)
   * that have no primitive analogue. */
  skip?: (line: string) => boolean;
}

/** Default rule set. Covers every native element that has a
 * direct `@fairfox/polly/ui` replacement. Consumers may extend
 * through the `additionalRules` option. */
export const DEFAULT_SHARED_COMPONENT_RULES: SharedComponentRule[] = [
  { pattern: /<button[\s>]/, element: "<button>", replacement: "<Button>" },
  {
    pattern: /<input[\s>/]/,
    element: "<input>",
    replacement: "<ActionInput> or <TextInput>",
    // `<input type="hidden">` has no primitive analogue and is a
    // legitimate way to carry form data.
    skip: (line) => /type=["']hidden["']/.test(line),
  },
  {
    pattern: /<textarea[\s>]/,
    element: "<textarea>",
    replacement: '<ActionInput variant="multi">',
  },
  { pattern: /<select[\s>]/, element: "<select>", replacement: "<Select>" },
  { pattern: /<form[\s>]/, element: "<form>", replacement: "<ActionForm>" },
  { pattern: /<dialog[\s>]/, element: "<dialog>", replacement: "<Modal>" },
];

/** One violation: a raw element found in an app source file. */
export interface SharedComponentViolation {
  /** Path relative to `root`. */
  file: string;
  /** 1-based line number. */
  line: number;
  /** Element marker, e.g. "<button>". */
  element: string;
  /** Suggested replacement. */
  replacement: string;
  /** Trimmed offending line for context. */
  content: string;
}

export interface CheckSharedComponentsOptions {
  /** Repository root. Violation file paths are reported relative to
   * this directory. */
  root: string;
  /** Directory under `root` to scan. Defaults to "packages". */
  scanRoot?: string;
  /** Directory names to skip entirely during traversal. Defaults to
   * node_modules / .git / dist / build / tests. */
  skipDirs?: Set<string>;
  /** Workspace package names (the directory names immediately under
   * `scanRoot`) to exempt. Useful for legacy packages that can't
   * migrate to the primitives yet. */
  exemptPackages?: Set<string>;
  /** Additional rules appended to {@link DEFAULT_SHARED_COMPONENT_RULES}. */
  additionalRules?: SharedComponentRule[];
  /** Override the default rule set entirely. If set,
   * `additionalRules` is ignored. */
  rules?: SharedComponentRule[];
}

const DEFAULT_SKIP_DIRS = new Set(["node_modules", ".git", "dist", "build", "tests"]);

export interface SharedComponentsCheckResult {
  violations: SharedComponentViolation[];
  print(log: (msg: string) => void): void;
}

/** Walk the configured directory, returning every violation found. */
export async function checkSharedComponents(
  options: CheckSharedComponentsOptions
): Promise<SharedComponentsCheckResult> {
  const rules = options.rules ?? [
    ...DEFAULT_SHARED_COMPONENT_RULES,
    ...(options.additionalRules ?? []),
  ];
  const skipDirs = options.skipDirs ?? DEFAULT_SKIP_DIRS;
  const scanRoot = options.scanRoot ?? "packages";
  const exemptPackages = options.exemptPackages ?? new Set<string>();
  const packagesPath = join(options.root, scanRoot);
  const violations: SharedComponentViolation[] = [];

  await scanDirectory(packagesPath, {
    root: options.root,
    packagesPath,
    skipDirs,
    exemptPackages,
    rules,
    violations,
  });

  return {
    violations,
    print(log) {
      if (violations.length === 0) {
        log("[shared-components] ok");
        return;
      }
      log(`[shared-components] ${violations.length} violation(s) found:\n`);
      for (const v of violations) {
        log(`  ${v.file}:${v.line} — ${v.element} → use ${v.replacement}`);
        log(`    ${v.content}\n`);
      }
      log("[shared-components] Use @fairfox/polly/ui primitives instead of native HTML elements.");
    },
  };
}

interface ScanState {
  root: string;
  packagesPath: string;
  skipDirs: Set<string>;
  exemptPackages: Set<string>;
  rules: SharedComponentRule[];
  violations: SharedComponentViolation[];
}

async function scanDirectory(dir: string, state: ScanState): Promise<void> {
  let entries: Dirent[];
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    const fullPath = join(dir, entry.name);
    if (entry.isDirectory()) {
      if (state.skipDirs.has(entry.name)) {
        continue;
      }
      if (dir === state.packagesPath && state.exemptPackages.has(entry.name)) {
        continue;
      }
      await scanDirectory(fullPath, state);
    } else if (entry.isFile() && (entry.name.endsWith(".tsx") || entry.name.endsWith(".jsx"))) {
      await scanFile(fullPath, state);
    }
  }
}

async function scanFile(filePath: string, state: ScanState): Promise<void> {
  const text = await Bun.file(filePath).text();
  const lines = text.split("\n");

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (!line) continue;
    const trimmed = line.trim();
    if (isCommentLine(trimmed)) continue;
    for (const rule of state.rules) {
      if (!matchesRule(line, rule)) continue;
      state.violations.push({
        file: relative(state.root, filePath),
        line: i + 1,
        element: rule.element,
        replacement: rule.replacement,
        content: trimmed,
      });
    }
  }
}

function isCommentLine(trimmed: string): boolean {
  return trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*");
}

function matchesRule(line: string, rule: SharedComponentRule): boolean {
  if (!rule.pattern.test(line)) return false;
  const commentIndex = line.indexOf("//");
  const elementIndex = line.search(rule.pattern);
  if (commentIndex !== -1 && commentIndex < elementIndex) return false;
  if (rule.skip?.(line)) return false;
  return true;
}
