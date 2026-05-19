/**
 * Five LLM-cliché checks bundled into `pollyCorePlugin`:
 *
 *   - polly:no-banners          — decorative comment dividers (`// ─────`, `// ====`)
 *   - polly:no-decorative-emoji — Unicode emoji used for visual flair
 *   - polly:no-marketing        — overused booster words and filler ("ensures that") // audit-allow: marketing
 *   - polly:no-note-prefix      — `// Note:` / `// Important:` / `// Warning:` / `// TIP:` / `// NB:`
 *   - polly:no-commented-code   — leading-keyword commented-out source lines
 *
 * Each is parameterised: defaults match polly's own zones and may be
 * overridden via `polly.config.ts`. Suppress per-line with a trailing
 * `// audit-allow: <kind>` marker, where `<kind>` is the rule's slug
 * (one of: banner, emoji, marketing, note-prefix, commented-code).
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";
import type { Check } from "../types";

const SKIP_DIRS_DEFAULT = ["node_modules", ".git", "dist", ".bun", ".cache", "build", "coverage"];
const DEFAULT_CODE_ZONES = ["src", "tools", "cli", "scripts", "recipes", "examples"];
const DEFAULT_CODE_EXTENSIONS = [".ts", ".tsx"];

const BANNER_RE = /^\s*\/\/.*(?:[=]{5,}|[-]{10,}|[─━═]{3,})/;
const DECORATIVE_EMOJI_RE = /[\u{1F680}\u{2728}\u{1F3AF}\u{1F389}\u{26A1}\u{1F4E6}\u{1F9E9}]/u;
const MARKETING_RE =
  /\b(comprehensive|robust|elegantly?|seamless(ly)?|leverages?|utili[sz]es?|ensures? that)\b/i; // audit-allow: marketing
const NOTE_PREFIX_RE = /^\s*\/\/\s*(Note|Important|Warning|TIP|NB)\s*:/;
const COMMENTED_CODE_RE =
  /^\s*\/\/\s+(import|const|let|var|function|class|return|if|for|while|export)\b/;

const ALLOW_LINE_RE = /\/\/\s*audit-allow:\s*([\w-]+)/;

function isLineAllowed(line: string, kind: string): boolean {
  const match = line.match(ALLOW_LINE_RE);
  return match !== null && match[1] === kind;
}

type ClicheConfig = {
  zones?: string[];
  skipDirs?: string[];
  allowFiles?: string[];
  /** File extensions to scan, defaulting to `.ts` and `.tsx`. */
  extensions?: string[];
};

function matchesExtension(name: string, extensions: Set<string>): boolean {
  const dotIdx = name.lastIndexOf(".");
  if (dotIdx < 0) return false;
  return extensions.has(name.slice(dotIdx));
}

async function walkFilesByExt(
  dir: string,
  skipDirs: Set<string>,
  extensions: Set<string>,
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
      if (skipDirs.has(entry.name) || entry.name.startsWith(".")) continue;
      await walkFilesByExt(fullPath, skipDirs, extensions, out);
    } else if (entry.isFile() && matchesExtension(entry.name, extensions)) {
      out.push(fullPath);
    }
  }
}

function resolveCliche(cfg: ClicheConfig | undefined): {
  zones: string[];
  skipDirs: Set<string>;
  allowFiles: Set<string>;
  extensions: Set<string>;
} {
  const c = cfg ?? {};
  return {
    zones: c.zones ?? DEFAULT_CODE_ZONES,
    skipDirs: new Set(c.skipDirs ?? SKIP_DIRS_DEFAULT),
    allowFiles: new Set(c.allowFiles ?? []),
    extensions: new Set(c.extensions ?? DEFAULT_CODE_EXTENSIONS),
  };
}

async function collectClicheFiles(
  rootDir: string,
  cfg: ClicheConfig | undefined
): Promise<{ files: string[]; allowFiles: Set<string> }> {
  const { zones, skipDirs, allowFiles, extensions } = resolveCliche(cfg);
  const files: string[] = [];
  for (const zone of zones) {
    await walkFilesByExt(join(rootDir, zone), skipDirs, extensions, files);
  }
  return { files, allowFiles };
}

function scanFile(content: string, rel: string, pattern: RegExp, allowKind: string): string[] {
  const out: string[] = [];
  const lines = content.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    if (pattern.test(line) && !isLineAllowed(line, allowKind)) {
      out.push(`${rel}:${i + 1}: ${line.trim()}`);
    }
  }
  return out;
}

function makeClicheCheck(
  id: string,
  description: string,
  pattern: RegExp,
  allowKind: string
): Check<ClicheConfig | undefined> {
  return {
    id,
    description,
    filesRead: async (cfg, root) => {
      const { files, allowFiles } = await collectClicheFiles(root, cfg);
      return files.filter((p) => !allowFiles.has(relative(root, p)));
    },
    run: async ({ rootDir, config }) => {
      const { files, allowFiles } = await collectClicheFiles(rootDir, config);
      const violations: string[] = [];
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (allowFiles.has(rel)) continue;
        const content = await Bun.file(filePath).text();
        violations.push(...scanFile(content, rel, pattern, allowKind));
      }
      return { ok: violations.length === 0, messages: violations };
    },
  };
}

const noBanners = makeClicheCheck(
  "polly:no-banners",
  "Ban decorative comment dividers (// ─────, // =====, // ----------)",
  BANNER_RE,
  "banner"
);

const noDecorativeEmoji = makeClicheCheck(
  "polly:no-decorative-emoji",
  "Ban a small set of Unicode emoji used as decorative flair in source",
  DECORATIVE_EMOJI_RE,
  "emoji"
);

const noNotePrefix = makeClicheCheck(
  "polly:no-note-prefix",
  "Ban `// Note:` / `// Important:` / `// Warning:` / `// TIP:` / `// NB:` comment prefixes",
  NOTE_PREFIX_RE,
  "note-prefix"
);

const noCommentedCode = makeClicheCheck(
  "polly:no-commented-code",
  "Ban single-line commented-out source (lines starting with `// import|const|let|...`)",
  COMMENTED_CODE_RE,
  "commented-code"
);

// polly:no-marketing scans code AND markdown by default — its zones and
// extensions are wider than the code-only checks above.

type MarketingConfig = ClicheConfig;

const DEFAULT_MARKETING_ZONES = [...DEFAULT_CODE_ZONES, "docs"];
const DEFAULT_MARKETING_EXTENSIONS = [".ts", ".tsx", ".md"];

function resolveMarketing(cfg: MarketingConfig | undefined): {
  zones: string[];
  skipDirs: Set<string>;
  allowFiles: Set<string>;
  extensions: Set<string>;
} {
  const c = cfg ?? {};
  return {
    zones: c.zones ?? DEFAULT_MARKETING_ZONES,
    skipDirs: new Set(c.skipDirs ?? SKIP_DIRS_DEFAULT),
    allowFiles: new Set(c.allowFiles ?? []),
    extensions: new Set(c.extensions ?? DEFAULT_MARKETING_EXTENSIONS),
  };
}

const noMarketing: Check<MarketingConfig | undefined> = {
  id: "polly:no-marketing",
  description:
    'Ban marketing language ("comprehensive / robust / seamless / leverages / ensures that") in source and docs', // audit-allow: marketing
  filesRead: async (cfg, root) => {
    const { zones, skipDirs, extensions, allowFiles } = resolveMarketing(cfg);
    const out: string[] = [];
    for (const zone of zones) {
      await walkFilesByExt(join(root, zone), skipDirs, extensions, out);
    }
    return out.filter((p) => !allowFiles.has(relative(root, p)));
  },
  run: async ({ rootDir, config }) => {
    const { zones, skipDirs, extensions, allowFiles } = resolveMarketing(config);
    const violations: string[] = [];
    for (const zone of zones) {
      const files: string[] = [];
      await walkFilesByExt(join(rootDir, zone), skipDirs, extensions, files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (allowFiles.has(rel)) continue;
        const content = await Bun.file(filePath).text();
        violations.push(...scanFile(content, rel, MARKETING_RE, "no-marketing"));
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

export const clicheCoreChecks: Check<unknown>[] = [
  noBanners as Check<unknown>,
  noDecorativeEmoji as Check<unknown>,
  noMarketing as Check<unknown>,
  noNotePrefix as Check<unknown>,
  noCommentedCode as Check<unknown>,
];
