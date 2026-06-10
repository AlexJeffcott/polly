/**
 * Zero-config tier discovery for a consumer's Polly project.
 *
 * `polly test --tier` from a consumer's project builds its {@link TierPlan} by
 * convention — no config required:
 *   - unit         `bun test` (or `bun test tests/unit` if that dir exists)
 *   - integration  `bun test tests/integration` (when the dir exists)
 *   - browser      the Polly browser runner over `*.browser.{ts,tsx}`
 *   - e2e          `scripts/e2e-*.{ts,tsx}` exporting `run(ctx)` — the same
 *                  contract Polly dogfoods, so consumer e2e scripts written with
 *                  `@fairfox/polly/test` helpers slot straight in.
 *
 * A tier only appears when its inputs exist, so a project with just unit tests
 * gets just a unit tier.
 */
import { existsSync } from "node:fs";
import { dirname, join } from "node:path";
import type { CaseSpec, Tier, TierPlan } from "./types";

/** Files matching `pattern` under `root`, excluding node_modules, sorted. */
async function globFiles(root: string, pattern: string): Promise<string[]> {
  const glob = new Bun.Glob(pattern);
  const out: string[] = [];
  for await (const file of glob.scan({ cwd: root, onlyFiles: true })) {
    if (file.includes("node_modules") || file.startsWith("dist/")) continue;
    out.push(file);
  }
  return out.sort();
}

/** Resolve the browser runner, preferring the bundled build. */
function browserRunner(): string {
  const bundled = `${import.meta.dir}/../browser/run.js`;
  const source = `${import.meta.dir}/../browser/run.ts`;
  return existsSync(bundled) ? bundled : source;
}

/** A safe directory to hand the browser runner (never the project root, which
 *  would make it scan node_modules). */
function browserDir(root: string, files: string[]): string {
  if (existsSync(join(root, "tests/browser"))) return "tests/browser";
  if (existsSync(join(root, "tests"))) return "tests";
  return dirname(files[0] ?? ".") || ".";
}

/** `scripts/e2e-foo-bar.ts` → `foo-bar`. */
function e2eId(file: string): string {
  const base = file.replace(/^.*\//, "").replace(/\.(ts|tsx)$/, "");
  return base.replace(/^e2e-/, "") || base;
}

export async function discoverPlan(root: string): Promise<TierPlan> {
  const tiers: Tier[] = [];

  const hasUnitDir = existsSync(join(root, "tests/unit"));
  const hasIntegrationDir = existsSync(join(root, "tests/integration"));
  const testFiles = await globFiles(root, "**/*.test.{ts,tsx}");

  if (hasUnitDir) {
    tiers.push({
      name: "unit",
      description: "bun test tests/unit",
      cases: [
        { id: "unit", exec: { kind: "command", argv: ["bun", "test", "tests/unit"], cwd: root } },
      ],
    });
  } else if (testFiles.length > 0) {
    tiers.push({
      name: "unit",
      description: `bun test (${testFiles.length} files)`,
      cases: [{ id: "unit", exec: { kind: "command", argv: ["bun", "test"], cwd: root } }],
    });
  }

  if (hasIntegrationDir) {
    tiers.push({
      name: "integration",
      description: "bun test tests/integration",
      cases: [
        {
          id: "integration",
          exec: { kind: "command", argv: ["bun", "test", "tests/integration"], cwd: root },
        },
      ],
    });
  }

  const browserFiles = await globFiles(root, "**/*.browser.{ts,tsx}");
  if (browserFiles.length > 0) {
    tiers.push({
      name: "browser",
      description: `Puppeteer over ${browserFiles.length} *.browser file(s)`,
      timeoutMs: 180_000,
      cases: [
        {
          id: "browser",
          needs: ["browser"],
          exec: {
            kind: "command",
            argv: ["bun", browserRunner(), browserDir(root, browserFiles)],
            cwd: root,
          },
        },
      ],
    });
  }

  const e2eFiles = await globFiles(root, "scripts/e2e-*.{ts,tsx}");
  if (e2eFiles.length > 0) {
    const cases: CaseSpec[] = e2eFiles.map((file) => ({
      id: e2eId(file),
      tags: ["e2e"],
      exec: { kind: "module", modulePath: join(root, file) },
    }));
    tiers.push({
      name: "e2e",
      description: `run()-export scripts (${e2eFiles.length})`,
      concurrency: 2,
      timeoutMs: 240_000,
      cases,
    });
  }

  return { tiers };
}
