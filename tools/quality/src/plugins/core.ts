/**
 * `pollyCorePlugin` — the polly-provided core plugin.
 *
 * Wraps the four checks polly already ships in `@fairfox/polly/quality`
 * into the new `Check` contract. The wrapping is purely adaptive: each
 * underlying function (`checkNoAsCasting`, `checkNoRequire`,
 * `checkSecrets`, `checkGitignoreCoversAllowlist`) keeps its existing
 * exports unchanged, so consumers wiring those up by hand continue to
 * work. The plugin path is the new way; the function path stays the
 * same.
 *
 * The CSS family and shared-components live in a separate `polly-ui`
 * plugin (#92–#94) because they belong to the styled-component
 * contract polly-ui owns. Issue #98's scope is the four core checks.
 */

import { join } from "node:path";
import { Glob } from "bun";
import { checkNoAsCasting } from "../no-as-casting";
import { checkNoRequire } from "../no-require";
import { checkGitignoreCoversAllowlist, checkSecrets } from "../secrets";
import type { Check, QualityPlugin } from "../types";
import { additionalCoreChecks } from "./core-checks";
import { extraCoreChecks } from "./extra-checks";

const DEFAULT_EXCLUDES = ["node_modules", "dist", ".git", ".bun", "dist-test", "build", "coverage"];

type ScanConfig = {
  exclude?: string[];
  excludePackages?: string[];
  excludeFiles?: string[];
  filePatterns?: string;
};

async function scanFiles(rootDir: string, cfg: ScanConfig): Promise<string[]> {
  const excludeDirs = new Set(cfg.exclude ?? DEFAULT_EXCLUDES);
  const excludePackages = new Set(cfg.excludePackages ?? []);
  const excludeFiles = new Set(cfg.excludeFiles ?? []);
  const pattern = cfg.filePatterns ?? "**/*.{ts,tsx}";
  const glob = new Glob(pattern);
  const out: string[] = [];
  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const rel = file.replace(`${rootDir}/`, "");
    const segments = rel.split("/");
    if (segments.some((s) => excludeDirs.has(s))) continue;
    if (excludePackages.size > 0 && segments.some((s) => excludePackages.has(s))) continue;
    const basename = segments[segments.length - 1] ?? "";
    if (excludeFiles.has(basename) || excludeFiles.has(rel)) continue;
    out.push(file);
  }
  return out;
}

function resolveScanConfig(config: ScanConfig | undefined): ScanConfig {
  return config ?? {};
}

const noAsCasting: Check<ScanConfig | undefined> = {
  id: "polly:no-as-casting",
  description: "Ban TypeScript `as` type assertions outside the allowed forms",
  filesRead: (cfg, root) => scanFiles(root, resolveScanConfig(cfg)),
  run: async ({ rootDir, config }) => {
    const cfg = resolveScanConfig(config);
    const result = await checkNoAsCasting({
      rootDir,
      exclude: cfg.exclude ?? DEFAULT_EXCLUDES,
      ...(cfg.excludePackages ? { excludePackages: cfg.excludePackages } : {}),
      ...(cfg.excludeFiles ? { excludeFiles: cfg.excludeFiles } : {}),
      ...(cfg.filePatterns ? { filePatterns: cfg.filePatterns } : {}),
    });
    return {
      ok: result.violations.length === 0,
      messages: result.violations.map(
        (v) => `${v.file}:${v.line}: ${v.content}${v.advice ? ` — ${v.advice}` : ""}`
      ),
    };
  },
};

const noRequire: Check<ScanConfig | undefined> = {
  id: "polly:no-require",
  description: "Ban CommonJS `require(...)` calls in TypeScript source",
  filesRead: (cfg, root) => scanFiles(root, resolveScanConfig(cfg)),
  run: async ({ rootDir, config }) => {
    const cfg = resolveScanConfig(config);
    const result = await checkNoRequire({
      rootDir,
      exclude: cfg.exclude ?? DEFAULT_EXCLUDES,
      ...(cfg.filePatterns ? { filePatterns: cfg.filePatterns } : {}),
    });
    return {
      ok: result.violations.length === 0,
      messages: result.violations.map((v) => `${v.file}:${v.line}: ${v.content}`),
    };
  },
};

type SecretsConfig = {
  configPath?: string;
  noGit?: boolean;
};

const secrets: Check<SecretsConfig | undefined> = {
  id: "polly:secrets",
  description: "Run `gitleaks detect` against the working tree",
  // gitleaks scans the working tree on disk; we declare the config file as
  // the only file input. Tool-version is captured via cacheKeyExtras so a
  // new gitleaks release re-scans even on identical config + tree.
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    if (!c.configPath) return [];
    return [join(root, c.configPath)];
  },
  cacheKeyExtras: (cfg) => ({
    noGit: (cfg ?? {}).noGit === false ? "false" : "true",
  }),
  run: async ({ rootDir, config }) => {
    const cfg = config ?? {};
    const result = await checkSecrets({
      root: rootDir,
      ...(cfg.configPath ? { configPath: cfg.configPath } : {}),
      ...(typeof cfg.noGit === "boolean" ? { noGit: cfg.noGit } : {}),
    });
    if (!result.binaryFound) {
      return {
        ok: false,
        messages: [
          "gitleaks is not on PATH. Install with `brew install gitleaks` (macOS) or from https://github.com/gitleaks/gitleaks/releases.",
        ],
      };
    }
    return {
      ok: result.exitCode === 0,
      messages:
        result.exitCode === 0 ? [] : [result.output.trim() || `gitleaks exited ${result.exitCode}`],
    };
  },
};

type GitignoreConfig = {
  tomlPath?: string;
  gitignorePath?: string;
  sectionStartMarkers?: string[];
  sectionEndMarkers?: string[];
};

const gitignoreCrossCheck: Check<GitignoreConfig | undefined> = {
  id: "polly:gitignore-cross-check",
  description:
    "Verify every gitleaks allowlist entry marked as gitignored is actually covered by .gitignore",
  filesRead: (cfg, root) => {
    const c = cfg ?? {};
    return [
      join(root, c.tomlPath ?? ".gitleaks.toml"),
      join(root, c.gitignorePath ?? ".gitignore"),
    ];
  },
  run: async ({ rootDir, config }) => {
    const cfg = config ?? {};
    const result = await checkGitignoreCoversAllowlist({
      root: rootDir,
      ...(cfg.tomlPath ? { tomlPath: cfg.tomlPath } : {}),
      ...(cfg.gitignorePath ? { gitignorePath: cfg.gitignorePath } : {}),
      ...(cfg.sectionStartMarkers ? { sectionStartMarkers: cfg.sectionStartMarkers } : {}),
      ...(cfg.sectionEndMarkers ? { sectionEndMarkers: cfg.sectionEndMarkers } : {}),
    });
    return {
      ok: result.missing.length === 0,
      messages:
        result.missing.length === 0
          ? []
          : [
              "Paths allowed by .gitleaks.toml are NOT covered by .gitignore:",
              ...result.missing.map((f) => `  ${f}`),
            ],
    };
  },
};

export const POLLY_CORE_VERSION = "0.44.0";

export const pollyCorePlugin: QualityPlugin = {
  name: "polly",
  version: POLLY_CORE_VERSION,
  checks: [
    noAsCasting as Check<unknown>,
    noRequire as Check<unknown>,
    secrets as Check<unknown>,
    gitignoreCrossCheck as Check<unknown>,
    ...additionalCoreChecks,
    ...extraCoreChecks,
  ],
};
