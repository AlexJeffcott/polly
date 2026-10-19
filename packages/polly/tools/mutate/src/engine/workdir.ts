/**
 * Scratch working directories. Each test process runs with a fresh, empty cwd
 * outside the project, so a mutant that turns a configured path into a
 * relative one writes into a throwaway directory instead of the repo.
 *
 * Bun reads two things from the cwd that the tests depend on, so the scratch
 * dir carries a copy of each:
 *
 *   tsconfig.json  `extends` the project's — Bun takes JSX settings
 *                  (jsxImportSource) from the cwd's tsconfig, not the file's
 *   bunfig.toml    the project's, re-rendered with every preload resolved to
 *                  an absolute path — Bun resolves bunfig preloads against
 *                  the cwd, even under `--config`
 *
 * Tests that read `process.cwd()` still break here. The engine detects that
 * from a red scratch baseline and runs that target in-tree instead.
 */
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

export interface Workdirs {
  root: string;
  /** A fresh cwd holding the project's tsconfig and bunfig. */
  create(): string;
  /** Remove one directory from `create()`. */
  release(dir: string): void;
  /** Remove every scratch directory. */
  remove(): void;
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function absolutePreload(spec: unknown, projectCwd: string): unknown {
  if (typeof spec !== "string") return spec;
  try {
    return Bun.resolveSync(spec, projectCwd);
  } catch {
    return spec;
  }
}

/** Resolve top-level `preload` and `[test].preload` (a string or a list) against the project. */
export function absolutiseBunfig(
  config: Record<string, unknown>,
  projectCwd: string
): Record<string, unknown> {
  const fix = (v: unknown) =>
    Array.isArray(v)
      ? v.map((s) => absolutePreload(s, projectCwd))
      : absolutePreload(v, projectCwd);
  const out: Record<string, unknown> = { ...config };
  if ("preload" in out) out["preload"] = fix(out["preload"]);
  const test = out["test"];
  if (isRecord(test) && "preload" in test) out["test"] = { ...test, preload: fix(test["preload"]) };
  return out;
}

const tomlKey = (k: string) => (/^[A-Za-z0-9_-]+$/.test(k) ? k : JSON.stringify(k));

function tomlValue(v: unknown): string {
  if (Array.isArray(v)) return `[${v.map(tomlValue).join(", ")}]`;
  if (isRecord(v)) {
    return `{ ${Object.entries(v)
      .map(([k, x]) => `${tomlKey(k)} = ${tomlValue(x)}`)
      .join(", ")} }`;
  }
  if (typeof v === "string") return JSON.stringify(v);
  return String(v);
}

/** TOML for the plain shapes a bunfig holds: scalars, arrays and nested tables. */
export function renderToml(config: Record<string, unknown>, prefix: string[] = []): string {
  const lines: string[] = [];
  const tables: [string, Record<string, unknown>][] = [];
  for (const [k, v] of Object.entries(config)) {
    if (isRecord(v)) tables.push([k, v]);
    else lines.push(`${tomlKey(k)} = ${tomlValue(v)}`);
  }
  const sections = tables.map(([k, v]) => {
    const path = [...prefix, k];
    return `[${path.map(tomlKey).join(".")}]\n${renderToml(v, path)}`;
  });
  return [lines.join("\n"), ...sections].filter(Boolean).join("\n\n");
}

export function createWorkdirs(projectCwd: string): Workdirs {
  const root = mkdtempSync(join(tmpdir(), "polly-mutate-"));
  const files: Record<string, string> = {};
  const tsconfig = join(projectCwd, "tsconfig.json");
  if (existsSync(tsconfig)) files["tsconfig.json"] = JSON.stringify({ extends: tsconfig });
  const bunfig = join(projectCwd, "bunfig.toml");
  if (existsSync(bunfig)) {
    const parsed: unknown = Bun.TOML.parse(readFileSync(bunfig, "utf8"));
    if (isRecord(parsed)) files["bunfig.toml"] = renderToml(absolutiseBunfig(parsed, projectCwd));
  }
  return {
    root,
    create() {
      mkdirSync(root, { recursive: true });
      const dir = mkdtempSync(join(root, "run-"));
      for (const [name, text] of Object.entries(files)) writeFileSync(join(dir, name), text);
      return dir;
    },
    release: (dir) => rmSync(dir, { recursive: true, force: true }),
    remove: () => rmSync(root, { recursive: true, force: true }),
  };
}
