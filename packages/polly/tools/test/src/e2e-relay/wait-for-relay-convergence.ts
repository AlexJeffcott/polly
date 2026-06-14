/**
 * @fairfox/polly/test/e2e-relay — convergence polling for the relay
 * transport. The node-side analogue of the mesh kit's
 * {@link waitForConvergence}: it polls a value reader per peer until a
 * predicate holds for all of them, or throws with a per-peer summary.
 *
 * Unlike the mesh kit this reads in-process Automerge handles rather than a
 * browser DOM, so the snapshot is whatever the caller's `read` returns —
 * typically `handle.doc()` or a `$peerState` signal's `.value`.
 */

import { resolveContext } from "../e2e-shared/timeout-context";

export interface RelayConvergenceTarget {
  /** Label for the failure summary. */
  peerId: string;
  /** Read this peer's current observed value. Returns undefined while the
   *  handle is still loading. */
  read: () => unknown;
}

export interface WaitForRelayConvergenceOptions {
  /** Cap wait time before throwing. Defaults to 10s. */
  timeoutMs?: number;
  /** Poll interval. Defaults to 50ms. */
  pollMs?: number;
  /**
   * Optional one-line diagnostic snapshot, evaluated ONLY on timeout and
   * appended to the failure. Use it to surface live transport state the
   * per-peer values can't show — e.g. `() => relayStats(server)` for the
   * relay's connected-client and document counts. A throwing or rejecting
   * context is swallowed so it can never mask the real timeout.
   */
  context?: () => string | Promise<string>;
}

/**
 * Block until `predicate` holds for every target's current value, or throw.
 */
export async function waitForRelayConvergence(
  targets: ReadonlyArray<RelayConvergenceTarget>,
  predicate: (value: unknown, peerId: string) => boolean,
  options: WaitForRelayConvergenceOptions = {}
): Promise<void> {
  const { timeoutMs = 10_000, pollMs = 50 } = options;
  const deadline = Date.now() + timeoutMs;
  let last: Array<{ peerId: string; value: unknown }> = [];

  while (Date.now() < deadline) {
    last = targets.map((t) => ({ peerId: t.peerId, value: t.read() }));
    if (last.every(({ value, peerId }) => predicate(value, peerId))) return;
    await new Promise((r) => setTimeout(r, pollMs));
  }

  const summary = last
    .map(({ peerId, value }) => `  ${peerId}: ${JSON.stringify(value)}`)
    .join("\n");
  const transport = await resolveContext(options.context);
  throw new Error(
    `waitForRelayConvergence: predicate did not hold for every peer within ${timeoutMs}ms.\n${summary}${transport}`
  );
}
