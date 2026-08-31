/**
 * Falsification test for the socket-error containment in
 * `createPeerStateClient`.
 *
 * automerge-repo's `WebSocketClientAdapter.onError` rethrows any carried
 * error whose `code` is not "ECONNREFUSED". Bun's WebSocket error event
 * carries no `code`, so before the containment every failed connect attempt
 * threw out of the listener — once per `retryInterval`, for as long as the
 * relay was unreachable. The throw arrives from the event loop, so nothing
 * catches it: under `bun test` it is charged to whichever test is running,
 * which is how one stalled relay test used to fail three unrelated tests in
 * other files.
 *
 * This test uses a real socket against a port nothing listens on. Remove the
 * `containSocketErrors` call in peer-relay-adapter.ts and it fails.
 */

import { describe, expect, test } from "bun:test";
import "@/shared/lib/wasm-init";
import { createPeerStateClient } from "@/shared/lib/peer-relay-adapter";

/** Port 1 is privileged, so no test process can be listening on it. */
const DEAD_URL = "ws://127.0.0.1:1/polly/peer";
const RETRY_INTERVAL_MS = 100;
/** Long enough for at least three connect attempts to fail. */
const OBSERVE_MS = 400;

describe("peer-relay client against an unreachable relay", () => {
  test("repeated connection failures are reported, not thrown", async () => {
    const errors: Error[] = [];
    const client = createPeerStateClient({
      url: DEAD_URL,
      retryInterval: RETRY_INTERVAL_MS,
      onSocketError: (error) => errors.push(error),
    });

    try {
      await new Promise((resolve) => setTimeout(resolve, OBSERVE_MS));

      // The report path fired, so the socket really did fail — the test is
      // not passing because nothing happened.
      expect(errors.length).toBeGreaterThan(0);
      expect(client.connectionState.value).toBe("disconnected");
    } finally {
      await client.close();
    }
  }, 15000);

  test("a client left to retry does not fail the next test", async () => {
    await new Promise((resolve) => setTimeout(resolve, OBSERVE_MS));
    expect(true).toBe(true);
  }, 15000);
});
