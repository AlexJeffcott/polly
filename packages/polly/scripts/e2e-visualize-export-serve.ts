#!/usr/bin/env bun
/**
 * E2e: `polly visualize export` → `serve`, from cold state.
 *
 * `e2e-visualize.ts` covers `generate` (DSL + structurizr-validate). The
 * downstream `export` (Docker → static site) and `serve` (view it) paths had
 * no cold coverage — and building this script surfaced that `export` was
 * broken: it ran the deprecated `structurizr/cli` with `-format static`,
 * which silently writes nothing and still exits 0, so `polly visualize
 * export` reported "✓ Static site generated" over an empty `docs/site`. The
 * fix (switch to the consolidated `structurizr/structurizr` image, which
 * implements the `static` exporter) is asserted here.
 *
 * Against a cold copy of `examples/minimal`, using the working-tree CLI:
 *
 *   1. `generate` produces `docs/architecture.dsl`.
 *   2. `export` exits 0 and writes a real static site — `docs/site/index.html`
 *      plus its asset bundle — not an empty directory.
 *   3. `serve --port=<ephemeral>` boots a static server; an HTTP GET returns
 *      200 and the served bytes are the exported `index.html`.
 *   4. Teeth: SIGTERM to the `polly` wrapper stops the server — the port
 *      stops answering. The wrapper used to die alone and orphan the
 *      `visualize serve` grandchild, which kept the port up and held this
 *      script's stdio pipes open, so it hung after printing PASS.
 *   5. Teeth: `export` with no DSL, and `serve` with no site, each exit
 *      non-zero rather than claiming success over nothing.
 *
 * The serve subprocess would otherwise `open` a real browser tab; the script
 * neutralises that by shadowing `open`/`xdg-open` with no-ops on PATH.
 *
 * Needs: Docker and the pinned `STRUCTURIZR_IMAGE` (tools/visualize/src/runner/export.ts).
 */

export const capability = "visualize.export-serve" as const;

import {
  chmodSync,
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { runCli } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const REPO_ROOT = resolve(import.meta.dir, "../../..");
const MINIMAL = join(REPO_ROOT, "examples/minimal");
const POLLY_CLI = resolve(import.meta.dir, "../cli/polly.ts");

function copyExample(dst: string): void {
  cpSync(MINIMAL, dst, {
    recursive: true,
    filter: (p) => {
      const base = p.split("/").pop();
      return base !== "node_modules" && base !== "dist" && base !== "docs";
    },
  });
}

/** A bin dir whose `open`/`xdg-open` are no-ops, so the serve subprocess
 *  does not pop a real browser tab. Returned PATH prefix is prepended. */
function noBrowserBin(parent: string): string {
  const bin = join(parent, "nobrowser-bin");
  mkdirSync(bin, { recursive: true });
  for (const name of ["open", "xdg-open"]) {
    const p = join(bin, name);
    writeFileSync(p, "#!/bin/sh\nexit 0\n");
    chmodSync(p, 0o755);
  }
  return bin;
}

async function probe(url: string, timeoutMs: number): Promise<string> {
  const deadline = Date.now() + timeoutMs;
  let lastErr: unknown;
  while (Date.now() < deadline) {
    try {
      const res = await fetch(url);
      if (res.ok) return await res.text();
      lastErr = `status ${res.status}`;
    } catch (err) {
      lastErr = err;
    }
    await new Promise((r) => setTimeout(r, 150));
  }
  throw new Error(`serve did not answer 200 at ${url} within ${timeoutMs}ms (${String(lastErr)})`);
}

/** Wait for `proc` to exit; SIGKILL it if it outlives `timeoutMs`. */
async function exitWithin(proc: Bun.Subprocess, timeoutMs: number): Promise<void> {
  let timer: ReturnType<typeof setTimeout> | undefined;
  const timedOut = new Promise<boolean>((r) => {
    timer = setTimeout(() => r(true), timeoutMs);
  });
  const outlived = await Promise.race([proc.exited.then(() => false), timedOut]);
  clearTimeout(timer);
  if (outlived) {
    proc.kill("SIGKILL");
    await proc.exited;
  }
}

/** True if `url` still gets any HTTP response once `windowMs` has passed. */
async function answersAfter(url: string, windowMs: number): Promise<boolean> {
  const deadline = Date.now() + windowMs;
  while (Date.now() < deadline) {
    try {
      await fetch(url, { signal: AbortSignal.timeout(500) });
    } catch {
      return false; // connection refused: nothing is listening
    }
    await new Promise((r) => setTimeout(r, 150));
  }
  return true;
}

/** Best-effort teardown of whatever still listens on `port` (a leaked
 *  grandchild), so a failing run does not leave a server behind. */
function killPortListener(port: number): void {
  const found = Bun.spawnSync(["lsof", "-ti", `tcp:${port}`, "-sTCP:LISTEN"]);
  for (const pid of found.stdout.toString().split("\n")) {
    const n = Number.parseInt(pid, 10);
    if (Number.isInteger(n) && n > 0) {
      try {
        process.kill(n, "SIGKILL");
      } catch {
        // already gone
      }
    }
  }
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = mkdtempSync(join(tmpdir(), "polly-e2e-viz-"));
  const appDir = join(temp, "minimal");

  try {
    copyExample(appDir);

    ctx.log("[e2e] polly visualize generate");
    const gen = await runCli(["visualize", "generate"], { cwd: appDir });
    assert(gen.exitCode === 0, `generate exited ${gen.exitCode}\n${gen.stderr}`);
    assert(existsSync(join(appDir, "docs/architecture.dsl")), "generate did not produce the DSL");

    ctx.log("[e2e] polly visualize export");
    const exp = await runCli(["visualize", "export"], { cwd: appDir });
    assert(exp.exitCode === 0, `export exited ${exp.exitCode}\n${exp.stdout}\n${exp.stderr}`);
    const indexPath = join(appDir, "docs/site/index.html");
    assert(existsSync(indexPath), "export reported success but produced no docs/site/index.html");
    const indexHtml = readFileSync(indexPath, "utf8");
    assert(
      indexHtml.length > 1000,
      `exported index.html is suspiciously small (${indexHtml.length} bytes)`
    );
    assert(/structurizr/i.test(indexHtml), "exported index.html is not a structurizr site");

    ctx.log("[e2e] polly visualize serve --port=<ephemeral> (GET → 200)");
    const port = 41000 + Math.floor(Math.random() * 2000);
    // stdio goes to a file, not a pipe: an orphaned grandchild holding the
    // write end of a pipe kept this script alive after it printed PASS.
    const serveLog = join(temp, "serve.log");
    const serve = Bun.spawn(["bun", POLLY_CLI, "visualize", "serve", `--port=${port}`], {
      cwd: appDir,
      stdout: Bun.file(serveLog),
      stderr: Bun.file(serveLog),
      env: { ...process.env, PATH: `${noBrowserBin(temp)}:${process.env["PATH"] ?? ""}` },
    });
    try {
      const body = await probe(`http://127.0.0.1:${port}/`, 10_000);
      assert(/structurizr/i.test(body), "served root is not the exported structurizr index");
    } finally {
      serve.kill();
      await exitWithin(serve, 5_000);
    }

    // Teeth: killing the `polly` wrapper must stop the server it spawned.
    // Before the wrapper relayed signals, SIGTERM orphaned the
    // `visualize serve` grandchild, which kept the port answering.
    ctx.log("[e2e] teeth: SIGTERM to the polly wrapper stops the server");
    const stillServing = await answersAfter(`http://127.0.0.1:${port}/`, 3_000);
    if (stillServing) {
      killPortListener(port);
      const log = existsSync(serveLog) ? readFileSync(serveLog, "utf8") : "";
      assert(
        false,
        `port ${port} still answers 3s after the polly wrapper exited — ` +
          `the wrapper orphaned its serve child (killed the listener in teardown)\n${log}`
      );
    }

    // Teeth: both downstream commands must refuse when their input is absent.
    ctx.log("[e2e] teeth: export with no DSL, serve with no site → non-zero");
    const bareDir = mkdtempSync(join(tmpdir(), "polly-e2e-viz-bare-"));
    try {
      const exportNoDsl = await runCli(["visualize", "export"], { cwd: bareDir });
      assert(exportNoDsl.exitCode !== 0, "export with no DSL should exit non-zero");
      const serveNoSite = await runCli(["visualize", "serve", `--port=${port}`], { cwd: bareDir });
      assert(serveNoSite.exitCode !== 0, "serve with no site should exit non-zero");
    } finally {
      rmSync(bareDir, { recursive: true, force: true });
    }

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(temp, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
