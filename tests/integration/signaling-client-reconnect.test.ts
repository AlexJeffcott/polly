/**
 * Integration test: MeshSignalingClient recovers from a server drop.
 *
 * Real deployments hand the signalling server restarts, network blips,
 * and load-balancer rolls. A production client that opens a WebSocket,
 * sends its join frame, and then lets the connection silently die on
 * server close is not something a user can tell apart from "the whole
 * thing broke." This test spins up the Elysia signalling plugin on a
 * fixed port, connects a MeshSignalingClient, stops the server, brings
 * it back up on the same port, and asserts the client has re-joined
 * without any intervention from the caller — the onOpen callback fires
 * twice and `isConnected` returns true again.
 *
 * Red against a MeshSignalingClient that only logs the close; green
 * once the client schedules a reconnect on every non-stopping close.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { Elysia } from "elysia";
import { signalingServer } from "@/elysia/signaling-server-plugin";
import { MeshSignalingClient } from "@/shared/lib/mesh-signaling-client";

interface RunningApp {
  stop: () => Promise<void>;
}

let pendingApps: Array<RunningApp> = [];

afterEach(async () => {
  for (const app of pendingApps) {
    try {
      await app.stop();
    } catch {
      // best effort
    }
  }
  pendingApps = [];
}, 10000);

function startSignaling(port: number): RunningApp {
  const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
  const handle: RunningApp = {
    stop: async () => {
      (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
      // Give the OS a tick to release the port before the next listen().
      await new Promise((r) => setTimeout(r, 100));
    },
  };
  pendingApps.push(handle);
  return handle;
}

function pickPort(): number {
  return 30000 + Math.floor(Math.random() * 10000);
}

describe("MeshSignalingClient reconnect", () => {
  test("re-joins automatically after the server restarts on the same port", async () => {
    const port = pickPort();
    let app = startSignaling(port);
    const url = `ws://127.0.0.1:${port}/polly/signaling`;

    let openCount = 0;
    const client = new MeshSignalingClient({
      url,
      peerId: "peer-reconnect",
      onSignal: () => {},
      onOpen: () => {
        openCount += 1;
      },
    });

    await client.connect();
    expect(openCount).toBe(1);
    expect(client.isConnected).toBe(true);

    // Server drops: restart on the same port after a brief gap.
    await app.stop();
    await new Promise((r) => setTimeout(r, 200));
    app = startSignaling(port);

    // Wait for the client to reconnect on its own. The exponential
    // backoff starts at 250ms, so a second onOpen call should land
    // inside a few seconds.
    const deadline = Date.now() + 10000;
    while (Date.now() < deadline) {
      if (openCount >= 2 && client.isConnected) {
        break;
      }
      await new Promise((r) => setTimeout(r, 100));
    }

    expect(openCount).toBeGreaterThanOrEqual(2);
    expect(client.isConnected).toBe(true);

    client.close();
  }, 20000);

  test("does not reconnect after an explicit close()", async () => {
    const port = pickPort();
    startSignaling(port);
    const url = `ws://127.0.0.1:${port}/polly/signaling`;

    let openCount = 0;
    const client = new MeshSignalingClient({
      url,
      peerId: "peer-explicit-close",
      onSignal: () => {},
      onOpen: () => {
        openCount += 1;
      },
    });

    await client.connect();
    expect(openCount).toBe(1);

    client.close();
    await new Promise((r) => setTimeout(r, 1000));

    // A reconnect would have produced a second onOpen by now.
    expect(openCount).toBe(1);
    expect(client.isConnected).toBe(false);
  }, 10000);
});
