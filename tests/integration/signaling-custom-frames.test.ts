/**
 * Integration test: custom-frame extensibility on the signalling socket.
 *
 * The signalling client and server both now tolerate frames whose `type`
 * is outside the built-in vocabulary (`join`, `signal`, `peers-present`,
 * `peer-joined`, `peer-left`, `error`). Consumers layer their own
 * application protocols on the existing socket through a matched pair
 * of hooks: `MeshSignalingClient`'s `onCustomFrame` / `sendCustom`, and
 * `signalingServer`'s `onCustomFrame` handler.
 *
 * This test exercises the round trip. The test server's custom handler
 * echoes any `{ type: "ping" }` frame back as `{ type: "pong", seq }`,
 * and the test asserts that a client that sends a ping receives the
 * pong through its `onCustomFrame` hook — proving both that the server
 * hook receives the frame and that the client hook sees the reply.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { Elysia } from "elysia";
import {
  type CustomFrameSocket,
  type CustomSignalingFrame,
  signalingServer,
} from "@/elysia/signaling-server-plugin";
import { MeshSignalingClient } from "@/shared/lib/mesh-signaling-client";

let pendingApps: Array<{ stop: () => Promise<void> }> = [];
let pendingClients: MeshSignalingClient[] = [];

afterEach(async () => {
  for (const client of pendingClients) {
    try {
      client.close();
    } catch {
      // best effort
    }
  }
  pendingClients = [];
  for (const app of pendingApps) {
    try {
      await app.stop();
    } catch {
      // best effort
    }
  }
  pendingApps = [];
}, 10000);

function pickPort(): number {
  return 30000 + Math.floor(Math.random() * 10000);
}

interface PongFrame {
  type: "pong";
  seq: number;
}

describe("custom signalling frames", () => {
  test("server hook receives custom frames and can reply through send", async () => {
    const port = pickPort();
    const seen: Array<{ peerId: string | undefined; frame: CustomSignalingFrame }> = [];
    const app = new Elysia()
      .use(
        signalingServer({
          path: "/polly/signaling",
          onCustomFrame: (socket: CustomFrameSocket, frame, peerId) => {
            seen.push({ peerId, frame });
            if (frame["type"] === "ping" && typeof frame["seq"] === "number") {
              socket.send({ type: "pong", seq: frame["seq"] });
            }
          },
        })
      )
      .listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
        await new Promise((r) => setTimeout(r, 100));
      },
    });

    const pongs: PongFrame[] = [];
    const client = new MeshSignalingClient({
      url: `ws://localhost:${port}/polly/signaling`,
      peerId: "peer-a",
      onSignal: () => {
        // unused
      },
      onCustomFrame: (frame) => {
        if (frame.type === "pong" && typeof frame["seq"] === "number") {
          pongs.push({ type: "pong", seq: frame["seq"] });
        }
      },
    });
    pendingClients.push(client);
    await client.connect();

    // Let the join frame reach the server before sending the custom one.
    await new Promise((r) => setTimeout(r, 50));

    expect(client.sendCustom("ping", { seq: 1 })).toBe(true);
    expect(client.sendCustom("ping", { seq: 2 })).toBe(true);

    // Wait for both pongs — short poll, long ceiling.
    const deadline = Date.now() + 2000;
    while (pongs.length < 2 && Date.now() < deadline) {
      await new Promise((r) => setTimeout(r, 25));
    }

    expect(pongs.map((p) => p.seq).sort()).toEqual([1, 2]);
    // The server's hook saw both pings, each tagged with the sender's
    // authenticated peer id from the join handshake.
    expect(seen.filter((s) => s.frame["type"] === "ping")).toHaveLength(2);
    expect(seen[0]?.peerId).toBe("peer-a");
  }, 10000);

  test("client drops malformed frames and passes plain objects with unknown types to the hook", async () => {
    const port = pickPort();
    // A server that forwards whatever `ping` it receives but also
    // sends a malformed frame (non-JSON string) once the client joins
    // to prove the client's hook is robust to garbage.
    const app = new Elysia()
      .use(
        signalingServer({
          path: "/polly/signaling",
          onCustomFrame: (socket, frame) => {
            if (frame["type"] === "ping") {
              socket.send({ type: "pong", seq: frame["seq"] });
              socket.send("not-json");
            }
          },
        })
      )
      .listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
        await new Promise((r) => setTimeout(r, 100));
      },
    });

    const pongs: number[] = [];
    const client = new MeshSignalingClient({
      url: `ws://localhost:${port}/polly/signaling`,
      peerId: "peer-b",
      onSignal: () => {},
      onCustomFrame: (frame) => {
        if (frame.type === "pong" && typeof frame["seq"] === "number") {
          pongs.push(frame["seq"]);
        }
      },
    });
    pendingClients.push(client);
    await client.connect();
    await new Promise((r) => setTimeout(r, 50));

    expect(client.sendCustom("ping", { seq: 99 })).toBe(true);

    const deadline = Date.now() + 2000;
    while (pongs.length < 1 && Date.now() < deadline) {
      await new Promise((r) => setTimeout(r, 25));
    }
    expect(pongs).toEqual([99]);
  }, 10000);
});
