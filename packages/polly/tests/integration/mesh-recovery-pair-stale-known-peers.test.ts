/**
 * Integration test for polly issue #103.
 *
 * The contract violation #103 reproduces lives in a place that
 * polly's normal `bun:test` rig cannot easily reach: WebRTC under
 * Bun. The two viable node-side `RTCPeerConnection` implementations
 * polly recommends — `werift` (pure-TS) and `@roamhq/wrtc` (native
 * binding) — each have a friction point inside `bun:test`. werift
 * pulls a transitive `ip@<=2.0.1` SSRF advisory that polly's deps
 * audit refuses to ship past, and `@roamhq/wrtc` is a NAPI module
 * that calls `uv_async_init` — a libuv function bun has not yet
 * shipped support for (tracked in oven-sh/bun#18546).
 *
 * Rather than allowlist the werift CVE inside polly's own
 * `bun:test` workspace, this test outsources the runtime mesh
 * exercise to `examples/mesh-recovery-pair/main.ts`. That example
 * runs as a standalone bun program, lives under `examples/` (which
 * polly's `scripts/check-deps-audit.ts` already excludes from
 * osv-scanner and which is outside the root `workspaces` array
 * `bun audit` walks), and ships werift as the example's own dep.
 * The example exits 0 when polly's mesh contract holds in the
 * failing-shape diff from #103, exit 1 when it breaks, and exit 2
 * when the example refuses to run under a known false-positive
 * condition.
 *
 * This test launches that example twice — once in the post-fix
 * shape (sweep enabled), once in the pre-fix-emulated shape (sweep
 * disabled via `POLLY_103_DISABLE_FIX=1`) — and asserts the
 * expected exit code for each. The pre-fix-emulated run is the
 * falsification gate the parent ticket asks for: if the same
 * harness passed against unfixed polly, the harness would not
 * exercise the bug. Both modes must produce their expected outcome
 * for this test to pass.
 *
 * The example's stdout transcript — the wire-level evidence the
 * ticket lists in item 2 — is captured by the spawn and printed on
 * failure so the actionable signal lands in the test log without
 * needing to re-run the example manually.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { spawn } from "node:child_process";
import { resolve } from "node:path";

const EXAMPLE_DIR = resolve(
  import.meta.dir,
  "..",
  "..",
  "..",
  "..",
  "examples",
  "mesh-recovery-pair"
);
const EXAMPLE_ENTRY = resolve(EXAMPLE_DIR, "main.ts");

interface RunResult {
  exitCode: number | null;
  stdout: string;
  stderr: string;
}

/** Spawn the runnable example with the given env overrides. The
 * example's expected lifecycle is 0–60s; we cap each invocation at
 * 75s so a hung subprocess produces a clean test failure instead of
 * a CI-level kill. */
function runExample(env: Record<string, string>): Promise<RunResult> {
  return new Promise((resolveResult, rejectResult) => {
    const child = spawn("bun", ["run", EXAMPLE_ENTRY], {
      cwd: EXAMPLE_DIR,
      env: { ...process.env, ...env },
      stdio: ["ignore", "pipe", "pipe"],
    });
    let stdout = "";
    let stderr = "";
    child.stdout?.on("data", (chunk: Buffer) => {
      stdout += chunk.toString();
    });
    child.stderr?.on("data", (chunk: Buffer) => {
      stderr += chunk.toString();
    });
    const timer = setTimeout(() => {
      child.kill("SIGTERM");
      rejectResult(new Error(`example timed out after 75s; stdout tail:\n${stdout.slice(-1000)}`));
    }, 75_000);
    child.on("exit", (code) => {
      clearTimeout(timer);
      resolveResult({ exitCode: code, stdout, stderr });
    });
    child.on("error", (err) => {
      clearTimeout(timer);
      rejectResult(err);
    });
  });
}

const liveChildren: Array<{ kill: () => void }> = [];

afterEach(() => {
  for (const child of liveChildren) {
    try {
      child.kill();
    } catch {
      // best effort
    }
  }
  liveChildren.length = 0;
}, 5_000);

describe("issue #103 — examples/mesh-recovery-pair contract harness", () => {
  test("post-fix path: the example exits 0 when the WebRTC adapter's keyringSource + periodic sweep are wired", async () => {
    const result = await runExample({});
    if (result.exitCode !== 0) {
      const summary = `example exit=${result.exitCode}\n--- stdout ---\n${result.stdout}\n--- stderr ---\n${result.stderr}`;
      expect(summary).toContain("SUCCESS — contract holds");
    }
    expect(result.exitCode).toBe(0);
  }, 90_000);

  test("pre-fix-emulated falsification: POLLY_103_DISABLE_FIX=1 deterministically reproduces the deadlock", async () => {
    const result = await runExample({ POLLY_103_DISABLE_FIX: "1" });
    // If this test ever flips to exit 0 under POLLY_103_DISABLE_FIX,
    // either the pre-fix-emulation knob no longer turns the sweep
    // off (a regression in the configurability) or the bug doesn't
    // live where this harness thinks it does (in which case the
    // post-fix test above is also no longer proof). Surface the
    // transcript so the next session can tell the two cases apart.
    if (result.exitCode === 0) {
      const summary = `pre-fix-emulated path UNEXPECTEDLY PASSED — the harness no longer exercises #103.\n--- stdout ---\n${result.stdout}\n--- stderr ---\n${result.stderr}`;
      expect(summary).toContain("FAILURE — contract violated");
    }
    expect(result.exitCode).toBe(1);
  }, 90_000);
});
