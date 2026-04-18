/**
 * Phase 2 integration test for the signalling-server Elysia plugin.
 *
 * Spins up a real Elysia app on a random port with the signalling
 * plugin mounted, connects two raw WebSocket clients, and verifies:
 *
 *   1. A peer that has not joined cannot send a signal (server replies
 *      with type: "error", reason: "not-joined").
 *   2. After both peers join, a signal sent from peer A targeted at
 *      peer B is delivered to peer B verbatim, with the sender id
 *      replaced by the authenticated id from A's join message.
 *   3. A signal sent to an unknown peer id returns an "unknown-target"
 *      error to the sender, not to anyone else.
 *   4. Disconnecting a peer removes it from the routing table, so
 *      subsequent signals to it return "unknown-target".
 *
 * The test uses Bun's native WebSocket on the client side because the
 * server is Elysia's native (Bun) WebSocket and the two are the
 * straightforward pairing under Bun.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { Elysia } from "elysia";
import { signalingServer } from "@/elysia/signaling-server-plugin";

let pendingApps: Array<{ stop: () => Promise<void> }> = [];

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

function pickPort(): number {
  return 30000 + Math.floor(Math.random() * 10000);
}

/** Open a WebSocket and return a small handle for sending and reading
 * messages one at a time. Resolves once the socket is open. */
function openSignalingClient(url: string): Promise<{
  send: (msg: unknown) => void;
  next: () => Promise<unknown>;
  close: () => void;
}> {
  return new Promise((resolve, reject) => {
    const ws = new WebSocket(url);
    const queue: unknown[] = [];
    const waiters: Array<(msg: unknown) => void> = [];

    ws.addEventListener("open", () => {
      resolve({
        send: (msg) => ws.send(typeof msg === "string" ? msg : JSON.stringify(msg)),
        next: () =>
          new Promise<unknown>((r) => {
            if (queue.length > 0) r(queue.shift());
            else waiters.push(r);
          }),
        close: () => ws.close(),
      });
    });

    ws.addEventListener("message", (ev) => {
      const data = typeof ev.data === "string" ? JSON.parse(ev.data) : ev.data;
      const waiter = waiters.shift();
      if (waiter) waiter(data);
      else queue.push(data);
    });

    ws.addEventListener("error", reject);
  });
}

async function waitForMessage(
  client: { next: () => Promise<unknown> },
  timeoutMs = 1000
): Promise<unknown> {
  return Promise.race([
    client.next(),
    new Promise<never>((_, reject) =>
      setTimeout(
        () => reject(new Error(`Timed out waiting for message after ${timeoutMs}ms`)),
        timeoutMs
      )
    ),
  ]);
}

// Drain peer-discovery frames (peers-present, peer-joined, peer-left)
// so tests that assert on the signal/error contract are not tripped up
// by the additive discovery protocol covered in
// signaling-peer-notifications.test.ts.
async function waitForNonDiscoveryMessage(
  client: { next: () => Promise<unknown> },
  timeoutMs = 1000
): Promise<unknown> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    const msg = await waitForMessage(client, deadline - Date.now());
    const type =
      typeof msg === "object" && msg !== null && "type" in msg
        ? (msg as { type: unknown }).type
        : undefined;
    if (type !== "peers-present" && type !== "peer-joined" && type !== "peer-left") {
      return msg;
    }
  }
  throw new Error(`waitForNonDiscoveryMessage timed out after ${timeoutMs}ms`);
}

describe("signalingServer plugin", () => {
  test("relays a signal from peer A to peer B after both have joined", async () => {
    const port = pickPort();
    const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
      },
    });

    const url = `ws://127.0.0.1:${port}/polly/signaling`;
    const alice = await openSignalingClient(url);
    const bob = await openSignalingClient(url);

    alice.send({ type: "join", peerId: "peer-alice" });
    bob.send({ type: "join", peerId: "peer-bob" });

    // Give the server a tick to register both joins.
    await new Promise((r) => setTimeout(r, 50));

    alice.send({
      type: "signal",
      peerId: "peer-alice",
      targetPeerId: "peer-bob",
      payload: { sdp: "v=0\r\n…" },
    });

    const received = (await waitForNonDiscoveryMessage(bob)) as unknown as {
      type: string;
      peerId: string;
      targetPeerId: string;
      payload: unknown;
    };
    expect(received.type).toBe("signal");
    expect(received.peerId).toBe("peer-alice");
    expect(received.targetPeerId).toBe("peer-bob");
    expect(received.payload).toEqual({ sdp: "v=0\r\n…" });

    alice.close();
    bob.close();
  });

  test("a peer that has not joined cannot send a signal", async () => {
    const port = pickPort();
    const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
      },
    });

    const url = `ws://127.0.0.1:${port}/polly/signaling`;
    const carol = await openSignalingClient(url);

    carol.send({
      type: "signal",
      peerId: "peer-carol",
      targetPeerId: "peer-other",
      payload: {},
    });

    const reply = (await waitForMessage(carol)) as unknown as { type: string; reason: string };
    expect(reply.type).toBe("error");
    expect(reply.reason).toBe("not-joined");

    carol.close();
  });

  test("a signal to an unknown target returns an unknown-target error to the sender", async () => {
    const port = pickPort();
    const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
      },
    });

    const url = `ws://127.0.0.1:${port}/polly/signaling`;
    const dave = await openSignalingClient(url);
    dave.send({ type: "join", peerId: "peer-dave" });
    await new Promise((r) => setTimeout(r, 50));

    dave.send({
      type: "signal",
      peerId: "peer-dave",
      targetPeerId: "peer-nobody",
      payload: { ice: "candidate" },
    });

    const reply = (await waitForNonDiscoveryMessage(dave)) as unknown as {
      type: string;
      reason: string;
      targetPeerId: string;
    };
    expect(reply.type).toBe("error");
    expect(reply.reason).toBe("unknown-target");
    expect(reply.targetPeerId).toBe("peer-nobody");

    dave.close();
  });

  test("the server replaces the sender id with the authenticated join id", async () => {
    const port = pickPort();
    const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
      },
    });

    const url = `ws://127.0.0.1:${port}/polly/signaling`;
    const eve = await openSignalingClient(url);
    const frank = await openSignalingClient(url);

    eve.send({ type: "join", peerId: "peer-eve" });
    frank.send({ type: "join", peerId: "peer-frank" });
    await new Promise((r) => setTimeout(r, 50));

    // Eve tries to impersonate Mallory in the message body.
    eve.send({
      type: "signal",
      peerId: "peer-mallory",
      targetPeerId: "peer-frank",
      payload: { evil: true },
    });

    const received = (await waitForNonDiscoveryMessage(frank)) as unknown as { peerId: string };
    // Server replaces with the authenticated peer id.
    expect(received.peerId).toBe("peer-eve");

    eve.close();
    frank.close();
  });

  test("disconnecting a peer removes it from the routing table", async () => {
    const port = pickPort();
    const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
    pendingApps.push({
      stop: async () => {
        (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
      },
    });

    const url = `ws://127.0.0.1:${port}/polly/signaling`;
    const grace = await openSignalingClient(url);
    const henry = await openSignalingClient(url);

    grace.send({ type: "join", peerId: "peer-grace" });
    henry.send({ type: "join", peerId: "peer-henry" });
    await new Promise((r) => setTimeout(r, 50));

    // Henry disconnects. The server's close handler runs asynchronously;
    // wait long enough for it to evict henry from the peer map.
    henry.close();
    await new Promise((r) => setTimeout(r, 500));

    // Grace tries to signal Henry; should get unknown-target.
    grace.send({
      type: "signal",
      peerId: "peer-grace",
      targetPeerId: "peer-henry",
      payload: {},
    });

    const reply = (await waitForNonDiscoveryMessage(grace)) as unknown as {
      type: string;
      reason: string;
    };
    expect(reply.type).toBe("error");
    expect(reply.reason).toBe("unknown-target");

    grace.close();
  });
});
