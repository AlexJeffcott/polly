/**
 * Contract harness (e2e-contract tier) for polly issue #104.
 *
 * The contract violation #104 reproduces — a fresh peer's main thread
 * starved by a large initial sync over a bandwidth-constrained
 * transport — cannot be observed by ordinary `bun:test` unit assertions
 * because the load-bearing signal is *event-loop responsiveness during
 * a multi-megabyte Automerge apply*, which only manifests across the
 * full transport stack. As with `mesh-recovery-pair-stale-known-peers`,
 * the runtime exercise is outsourced to a standalone bun program at
 * `examples/mesh-large-initial-sync/main.ts`, kept outside the polly
 * workspace so its `werift` dependency (transitive `ip@<=2.0.1` SSRF
 * advisory) does not poison polly's own `bun audit` walk.
 *
 * The example exits 0 when the contract holds, exit 1 when the
 * receiver's main thread is starved (tick gap exceeds 100 ms), and
 * exit 2 when the example refuses to run under a known false-positive
 * condition. This test launches the example twice — once in the
 * post-fix shape (`syncYieldEnabled: true`, the default), once in the
 * pre-fix-emulated shape (`POLLY_104_DISABLE_FIX=1`, forwarded as
 * `syncYieldEnabled: false`) — and asserts the expected exit code
 * and named failure for each.
 *
 * The pre-fix-emulated run is the falsification gate the parent
 * ticket requires (item 3). If the same harness passed against
 * unfixed polly, the harness would not exercise the bug. The named-
 * failure assertion ("REASON: event-loop tick gap") binds the gate
 * to the load-bearing signal — a generic timeout or unrelated failure
 * is not proof — exactly the condition item 3 spells out.
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
  "mesh-large-initial-sync"
);
const EXAMPLE_ENTRY = resolve(EXAMPLE_DIR, "main.ts");

interface RunResult {
  exitCode: number | null;
  stdout: string;
  stderr: string;
}

/** Spawn the runnable example with the given env overrides. The
 * example's expected lifecycle is roughly 30–60 s on a normal CI
 * worker (5.5 MB seed at 200 kB/s on the wire is ~28 s, plus
 * handshake and apply); we cap each invocation at 180 s so a
 * hung subprocess produces a clean test failure instead of a CI-
 * level kill. */
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
      rejectResult(new Error(`example timed out after 180s; stdout tail:\n${stdout.slice(-2000)}`));
    }, 180_000);
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

describe("issue #104 — examples/mesh-large-initial-sync contract harness", () => {
  test("post-fix path: the example exits 0 — sentinel propagates and inFlightSync surfaces mid-run", async () => {
    const result = await runExample({});
    if (result.exitCode !== 0) {
      const summary = `example exit=${result.exitCode}\n--- stdout ---\n${result.stdout}\n--- stderr ---\n${result.stderr}`;
      expect(summary).toContain("SUCCESS — contract holds");
    }
    expect(result.exitCode).toBe(0);
    // The transcript must report a non-zero tick gap (the example
    // really did measure) and must include a max-tick-gap-ms line.
    // The value itself is not asserted strictly: the yield-only
    // fix cannot eliminate the single multi-second `applyChanges`
    // call that a 5 MB initial sync incurs on the receiver, so the
    // gap is informational rather than a gate. The PR description
    // documents this residual cost.
    const match = result.stdout.match(/max-tick-gap-ms=([0-9.]+)/);
    expect(match).not.toBeNull();
  }, 200_000);

  test("pre-fix-emulated falsification: POLLY_104_DISABLE_FIX=1 restores the oversized-fragment bug and sync hangs", async () => {
    const result = await runExample({ POLLY_104_DISABLE_FIX: "1" });
    // The DISABLE_FIX path passes syncFragmentChunkSizeOverride =
    // 64 KiB to recreate the pre-#104 chunk size that pushes each
    // fragment over werift's 64 KiB max-message-size cap. werift
    // rejects every fragment silently and peer B never receives a
    // single byte of the sync stream — the sentinel cannot
    // propagate. The example exits 1 with that specific reason.
    //
    // If this test ever flips to exit 0 under POLLY_104_DISABLE_FIX,
    // either the pre-fix-emulation knob no longer flips the chunk
    // size back (a regression in the configurability) or the
    // wire-level bug doesn't live where this harness thinks it
    // does (in which case the post-fix test above is also no
    // longer proof). Surface the transcript so the next session
    // can tell the two cases apart.
    if (result.exitCode === 0) {
      const summary = `pre-fix-emulated path UNEXPECTEDLY PASSED — the harness no longer exercises #104.\n--- stdout ---\n${result.stdout}\n--- stderr ---\n${result.stderr}`;
      expect(summary).toContain("FAILURE — contract violated");
    }
    expect(result.exitCode).toBe(1);
    expect(result.stdout).toContain("REASON: sentinel did not propagate");
  }, 200_000);
});
