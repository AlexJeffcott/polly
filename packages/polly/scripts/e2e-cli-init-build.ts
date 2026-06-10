#!/usr/bin/env bun
/**
 * E2e: `polly init` → build, from cold state.
 *
 * `polly init my-app && cd my-app && build` is the literal first thing a new
 * user does, and nothing verified it cold. Building this script paid for
 * itself twice over: it surfaced that `polly init` advertised four project
 * types but shipped only the `pwa` template (default `extension` pointed at a
 * missing directory), and that the pwa scaffold did not pass a strict `tsc`
 * because its worker tsconfig loaded DOM and WebWorker libs together — both
 * now fixed (the workers compile under a separate `tsconfig.worker.json`).
 *
 * What this asserts, cold, in a throwaway dir using the working-tree CLI:
 *
 *   1. `polly init app --type=pwa` exits 0 and produces the expected scaffold
 *      files.
 *   2. The negative path: `polly init … --type=extension` (a type with no
 *      template) exits non-zero, names the available types, and creates NO
 *      directory. This is the regression guard for the availability bug.
 *   3. With the scaffold's `@fairfox/polly` pinned to THIS checkout (so the
 *      build resolves the working tree offline, not a published release),
 *      `bun install`, `bun run build`, and the strict `bun run typecheck`
 *      (both tsconfigs) all exit 0 and `dist/` is emitted.
 */

export const capability = "cli.init-build" as const;

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { POLLY_PKG_DIR, runBun, runCli, withTempDir } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const EXPECTED_FILES = [
  "package.json",
  "index.html",
  "tsconfig.json",
  "build.ts",
  "src/main.ts",
  "src/service-worker.ts",
  "public/manifest.json",
];

/** Point the scaffold's @fairfox/polly dependency at the working tree so the
 *  build resolves this checkout offline rather than a published version. */
function pinPollyToWorkingTree(projectDir: string): void {
  const pkgPath = join(projectDir, "package.json");
  const pkg = JSON.parse(readFileSync(pkgPath, "utf-8")) as {
    dependencies?: Record<string, string>;
  };
  pkg.dependencies ??= {};
  pkg.dependencies["@fairfox/polly"] = `file:${POLLY_PKG_DIR}`;
  writeFileSync(pkgPath, JSON.stringify(pkg, null, 2));
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = withTempDir();

  try {
    // 1. Scaffold the pwa project.
    ctx.log("[e2e] polly init app --type=pwa");
    const init = await runCli(["init", "app", "--type=pwa"], { cwd: temp.dir });
    assert(init.exitCode === 0, `init exited ${init.exitCode}\n${init.stdout}\n${init.stderr}`);
    const appDir = join(temp.dir, "app");
    for (const file of EXPECTED_FILES) {
      assert(existsSync(join(appDir, file)), `scaffold missing ${file}`);
    }

    // 2. Negative path: a type with no template must error and create nothing.
    ctx.log("[e2e] polly init nope --type=extension (expect clean rejection)");
    const bad = await runCli(["init", "nope", "--type=extension"], { cwd: temp.dir });
    assert(bad.exitCode !== 0, "init with an unavailable type should exit non-zero");
    assert(
      !existsSync(join(temp.dir, "nope")),
      "init with an unavailable type must not create a directory"
    );
    const badOutput = `${bad.stdout}\n${bad.stderr}`;
    assert(
      /available/i.test(badOutput) && /pwa/.test(badOutput),
      `rejection should name the available types; got:\n${badOutput}`
    );

    // 3. Install (working-tree polly) and build.
    ctx.log("[e2e] pinning @fairfox/polly to the working tree; bun install");
    pinPollyToWorkingTree(appDir);
    const install = await runBun(["install"], { cwd: appDir });
    assert(install.exitCode === 0, `bun install exited ${install.exitCode}\n${install.stderr}`);

    ctx.log("[e2e] bun run build");
    const build = await runBun(["run", "build"], { cwd: appDir });
    assert(
      build.exitCode === 0,
      `bun run build exited ${build.exitCode}\n${build.stdout}\n${build.stderr}`
    );
    assert(
      existsSync(join(appDir, "dist", "src", "main.js")),
      "build did not emit dist/src/main.js"
    );

    // The scaffold must also pass its own strict typecheck. The pwa template
    // splits DOM and WebWorker into separate tsconfigs (the workers compile
    // under tsconfig.worker.json) so service-worker/shared-worker globals
    // resolve correctly.
    ctx.log("[e2e] bun run typecheck (both tsconfigs)");
    const tc = await runBun(["run", "typecheck"], { cwd: appDir });
    assert(
      tc.exitCode === 0,
      `scaffold typecheck failed (exit ${tc.exitCode})\n${tc.stdout}\n${tc.stderr}`
    );

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    temp.cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
