/**
 * @fairfox/polly/test/e2e-mesh — withRelay helper.
 *
 * Boots a polly signalling relay on an ephemeral port for e2e scripts.
 * The relay is the same Elysia plugin polly ships at runtime, so a script
 * driving the relay through `withRelay` exercises the production protocol
 * with no shimming. Two modes:
 *
 * - "embedded" (default): start an Elysia app on a kernel-assigned port and return
 *   its URL plus a close callback. The hermetic mode the suite runs in
 *   by default; depending on a staging relay would couple CI reliability
 *   to a network service we do not control.
 *
 * - "env": read SIGNALING_URL from the environment and return that
 *   alongside a no-op close. The override the nightly cron uses to smoke
 *   the production protocol against the live relay.
 *
 * Lift source: tests/integration/signaling-server.test.ts is the existing
 * recipe; this helper centralises it so every e2e script wires the relay
 * the same way.
 */

import { Elysia } from "elysia";
import { signalingServer } from "../../../../src/elysia/signaling-server-plugin";
import { resolveListenPort } from "../e2e-shared/ephemeral-port";

export interface WithRelayResult {
  /** WebSocket URL of the signalling endpoint, ready to be passed to
   *  `createMeshClient({ signaling: { url, peerId } })`. */
  url: string;
  /** Stop the relay. Idempotent; safe to call after a failed boot. */
  close: () => Promise<void>;
}

export interface WithRelayOptions {
  /**
   * "embedded" boots a fresh relay on an ephemeral port and returns its
   * URL. "env" reads SIGNALING_URL from the environment and returns it
   * without booting anything. Defaults to "embedded".
   */
  mode?: "embedded" | "env";
  /** Path under which the signalling endpoint is mounted. Defaults to
   *  "/polly/signaling" — the same default the SPA wiring uses. */
  path?: string;
}

/**
 * Start a signalling relay for the duration of an e2e script.
 *
 * @example
 * ```typescript
 * const relay = await withRelay();
 * try {
 *   // boot peers pointing signaling.url at relay.url ...
 * } finally {
 *   await relay.close();
 * }
 * ```
 */
export async function withRelay(options: WithRelayOptions = {}): Promise<WithRelayResult> {
  const mode = options.mode ?? "embedded";
  const path = options.path ?? "/polly/signaling";

  if (mode === "env") {
    const url = process.env["SIGNALING_URL"];
    if (!url) {
      throw new Error(
        "withRelay({ mode: 'env' }) requires SIGNALING_URL to be set in the environment."
      );
    }
    return {
      url,
      close: async () => {
        // env mode doesn't own a server, so close is a no-op.
      },
    };
  }

  // Port 0: the kernel assigns a free port and the relay owns it from that
  // moment, so no collision window exists for another process to win
  // (polly#174).
  const app = new Elysia().use(signalingServer({ path })).listen(0);
  const url = `ws://127.0.0.1:${resolveListenPort(app)}${path}`;

  return {
    url,
    close: async () => {
      // Elysia exposes the underlying Bun server here. The .stop(true)
      // force-closes any open connections so a hung peer cannot keep the
      // server alive past the script's intended lifetime.
      (
        app as unknown as {
          server?: { stop?: (force?: boolean) => void };
        }
      ).server?.stop?.(true);
    },
  };
}
