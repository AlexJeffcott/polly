/**
 * `pollyUiPlugin` — the polly-ui-provided plugin (#89, #90, #91–#94).
 *
 * Re-homes the CSS conformance family and shared-components ban under a
 * dedicated `polly-ui` namespace, and adds a new `no-inline-handlers`
 * check for JSX event handlers. Every wrap reuses the underlying
 * function from `tools/quality/src/css/*` and
 * `tools/quality/src/check-shared-components.ts` so behaviour is
 * identical to the pre-host invocation; only the integration surface
 * changes.
 *
 * Out of scope for this release:
 *   - The data-action dispatcher *runtime* described in #90. The check
 *     ships here so a project can ban inline handlers today; the
 *     dispatcher needs a real Preact implementation that mounts near
 *     <OverlayRoot> and registers a delegated event listener, and that
 *     work belongs in `src/polly-ui/actions.tsx` rather than under the
 *     quality plugin host. The check on its own is useful — it forces
 *     the consumer to pick an alternative — and the runtime can land
 *     in a follow-up release without changing the check's id.
 *   - Registry-driven CSS validation. The four CSS checks currently
 *     parse polly-ui's CSS at scan time. The new
 *     `@fairfox/polly/ui/registry` (introduced alongside this plugin)
 *     exposes the canonical token + component lists as data, and a
 *     follow-up can swap the parse-time discovery for a registry
 *     lookup. The shape of the wraps does not change when that
 *     happens; only the inner implementation does.
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";
import { Glob } from "bun";
import { checkSharedComponents } from "../check-shared-components";
import { checkCssLayout } from "../css/check-layout";
import { checkCssQuality } from "../css/check-quality";
import { checkCssUnused } from "../css/check-unused";
import { checkCssVars } from "../css/check-vars";
import type { Check, QualityPlugin } from "../types";

const SKIP_DIRS_DEFAULT = ["node_modules", ".git", "dist", ".bun", ".cache"];

function isCommentLine(trimmed: string): boolean {
  return trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*");
}

function isAllowedByGlob(rel: string, globs: string[]): boolean {
  for (const g of globs) {
    if (new Glob(g).match(rel)) return true;
  }
  return false;
}

async function walkScannableFiles(
  dir: string,
  skipDirs: Set<string>,
  exts: string[],
  out: string[]
): Promise<void> {
  let entries: import("node:fs").Dirent[];
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    const fullPath = join(dir, entry.name);
    if (entry.isDirectory()) {
      if (!skipDirs.has(entry.name)) await walkScannableFiles(fullPath, skipDirs, exts, out);
    } else if (entry.isFile() && exts.some((e) => entry.name.endsWith(e))) {
      out.push(fullPath);
    }
  }
}

// ─────────────────────────────────────────────────────────────────
// polly-ui:css-layout (#91)
// ─────────────────────────────────────────────────────────────────

type CssCheckConfig = {
  rootDir?: string;
  skipDirs?: string[];
};

const cssLayout: Check<CssCheckConfig | undefined> = {
  id: "polly-ui:css-layout",
  description: "Enforce that layout values come from the <Layout> primitive, not ad-hoc CSS",
  run: async ({ rootDir, config }) => {
    const r = await checkCssLayout({
      rootDir,
      ...(config?.skipDirs ? { skipDirs: config.skipDirs } : {}),
    });
    return {
      ok: r.violations.length === 0,
      messages: r.violations.map((v) => `${v.file}:${v.line}: ${v.rule}`),
    };
  },
};

const cssQuality: Check<CssCheckConfig | undefined> = {
  id: "polly-ui:css-quality",
  description: "Enforce that styled values come from semantic tokens, not literals",
  run: async ({ rootDir, config }) => {
    const r = await checkCssQuality({
      rootDir,
      ...(config?.skipDirs ? { skipDirs: config.skipDirs } : {}),
    });
    return {
      ok: r.violations.length === 0,
      messages: r.violations.map((v) => `${v.file}:${v.line}: ${v.rule}`),
    };
  },
};

const cssVars: Check<CssCheckConfig | undefined> = {
  id: "polly-ui:css-vars",
  description: "Flag `var(--name)` references that resolve to no `--name:` definition",
  run: async ({ rootDir, config }) => {
    const r = await checkCssVars({
      rootDir,
      ...(config?.skipDirs ? { skipDirs: config.skipDirs } : {}),
    });
    return {
      ok: r.violations.length === 0,
      messages: r.violations.map((v) => `${v.file}:${v.line}: ${v.rule}`),
    };
  },
};

const cssUnused: Check<CssCheckConfig | undefined> = {
  id: "polly-ui:css-unused",
  description: "Surface CSS-module selectors that are never referenced from JS/TSX (advisory)",
  run: async ({ rootDir, config }) => {
    const r = await checkCssUnused({
      rootDir,
      ...(config?.skipDirs ? { skipDirs: config.skipDirs } : {}),
    });
    return {
      // Advisory: never fails the run, just reports.
      ok: true,
      messages: r.violations.map((v) => `${v.file}:${v.line}: ${v.rule}`),
    };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly-ui:shared-components (#92)
// ─────────────────────────────────────────────────────────────────

type SharedComponentsConfig = {
  scanRoot?: string;
  skipDirs?: string[];
  exemptPackages?: string[];
};

const sharedComponents: Check<SharedComponentsConfig | undefined> = {
  id: "polly-ui:shared-components",
  description:
    "Ban native interactive HTML elements; require the polly-ui primitive (<Button>, <Modal>, etc.)",
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const r = await checkSharedComponents({
      root: rootDir,
      ...(c.scanRoot ? { scanRoot: c.scanRoot } : {}),
      ...(c.skipDirs ? { skipDirs: new Set(c.skipDirs) } : {}),
      ...(c.exemptPackages ? { exemptPackages: new Set(c.exemptPackages) } : {}),
    });
    return {
      ok: r.violations.length === 0,
      messages: r.violations.map(
        (v) => `${v.file}:${v.line}: ${v.element} → ${v.replacement} — ${v.content}`
      ),
    };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly-ui:no-inline-handlers (#90, check-only — runtime is a follow-up)
// ─────────────────────────────────────────────────────────────────

type NoInlineHandlersConfig = {
  banned?: string[];
  allowedFiles?: string[];
  zones?: string[];
  skipDirs?: string[];
};

const DEFAULT_NO_INLINE_HANDLERS: Required<NoInlineHandlersConfig> = {
  banned: [
    "onClick",
    "onSubmit",
    "onChange",
    "onInput",
    "onFocus",
    "onBlur",
    "onKeyDown",
    "onKeyUp",
    "onMouseDown",
    "onMouseUp",
    "onMouseEnter",
    "onMouseLeave",
  ],
  allowedFiles: [],
  zones: ["src"],
  skipDirs: SKIP_DIRS_DEFAULT,
};

function escapeRegex(name: string): string {
  return name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function buildHandlerRegex(banned: string[]): RegExp {
  const alts = banned.map(escapeRegex).join("|");
  // Match `onClick={…}` and `onClick="…"` and `onClick='…'` opening forms.
  // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp
  return new RegExp(`\\b(${alts})\\s*=\\s*\\{`);
}

function isTestFile(rel: string): boolean {
  return (
    rel.includes("__tests__") ||
    rel.includes(".test.") ||
    rel.includes(".spec.") ||
    rel.startsWith("tests/")
  );
}

async function scanFileForInlineHandlers(
  filePath: string,
  rel: string,
  regex: RegExp
): Promise<string[]> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    if (isCommentLine(line.trim())) continue;
    if (regex.test(line)) {
      out.push(`${rel}:${i + 1}: ${line.trim()}`);
    }
  }
  return out;
}

const noInlineHandlers: Check<NoInlineHandlersConfig | undefined> = {
  id: "polly-ui:no-inline-handlers",
  description:
    "Ban inline JSX event handlers (use data-action delegation instead — see polly-ui actions runtime)",
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_NO_INLINE_HANDLERS.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_NO_INLINE_HANDLERS.allowedFiles;
    const out: string[] = [];
    for (const z of c.zones ?? DEFAULT_NO_INLINE_HANDLERS.zones) {
      await walkScannableFiles(join(root, z), skipDirs, [".tsx"], out);
    }
    return out.filter((p) => {
      const rel = relative(root, p);
      return !isTestFile(rel) && !isAllowedByGlob(rel, allowed);
    });
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const banned = c.banned ?? DEFAULT_NO_INLINE_HANDLERS.banned;
    if (banned.length === 0) return { ok: true, messages: [] };
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_NO_INLINE_HANDLERS.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_NO_INLINE_HANDLERS.allowedFiles;
    const regex = buildHandlerRegex(banned);
    const violations: string[] = [];
    for (const z of c.zones ?? DEFAULT_NO_INLINE_HANDLERS.zones) {
      const files: string[] = [];
      await walkScannableFiles(join(rootDir, z), skipDirs, [".tsx"], files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (isTestFile(rel) || isAllowedByGlob(rel, allowed)) continue;
        violations.push(...(await scanFileForInlineHandlers(filePath, rel, regex)));
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

// ─────────────────────────────────────────────────────────────────

export const POLLY_UI_PLUGIN_VERSION = "0.46.0";

export const pollyUiPlugin: QualityPlugin = {
  name: "polly-ui",
  version: POLLY_UI_PLUGIN_VERSION,
  checks: [
    cssLayout as Check<unknown>,
    cssQuality as Check<unknown>,
    cssVars as Check<unknown>,
    cssUnused as Check<unknown>,
    sharedComponents as Check<unknown>,
    noInlineHandlers as Check<unknown>,
  ],
};
