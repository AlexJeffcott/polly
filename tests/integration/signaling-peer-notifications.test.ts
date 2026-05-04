/**
 * Integration test for the signalling server's peer-discovery protocol.
 *
 * Spins up a real Elysia app on a random port with the signalling
 * plugin mounted, connects raw WebSocket clients, and verifies the
 * frames emitted by the server through the lifecycle of a peer:
 *
 *   - On join, the newcomer receives `{type:"peers-present", peerIds:[...]}`
 *     once, listing every peer already joined at that moment.
 *   - On join, every incumbent receives `{type:"peer-joined", peerId:<newcomer>}`.
 *   - On close, every remaining incumbent receives
 *     `{type:"peer-left", peerId:<departed>}`.
 *
 * These frames are what turns the adapter's one-shot startup sweep into
 * a fully reactive discovery flow. Together with the existing
 * signal/error protocol (covered by signaling-server.test.ts) they are
 * the complete server-to-client surface.
 *
 * The test uses Bun's native WebSocket for the clients, same as the
 * existing signalling-server suite.
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

function mountSignalingApp(port: number): { url: string } {
  const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
  pendingApps.push({
    stop: async () => {
      (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
    },
  });
  return { url: `ws://127.0.0.1:${port}/polly/signaling` };
}

interface SignalingClient {
  send: (msg: unknown) => void;
  next: () => Promise<unknown>;
  drain: () => unknown[];
  close: () => void;
}

function openSignalingClient(url: string): Promise<SignalingClient> {
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
        drain: () => {
          const copy = queue.slice();
          queue.length = 0;
          return copy;
        },
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

interface PeersPresentFrame {
  type: "peers-present";
  peerIds: string[];
}

interface PeerJoinedFrame {
  type: "peer-joined";
  peerId: string;
}

interface PeerLeftFrame {
  type: "peer-left";
  peerId: string;
}

function isPeersPresent(value: unknown): value is PeersPresentFrame {
  return (
    typeof value === "object" &&
    value !== null &&
    "type" in value &&
    (value as unknown as { type: unknown }).type === "peers-present"
  );
}

function isPeerJoined(value: unknown): value is PeerJoinedFrame {
  return (
    typeof value === "object" &&
    value !== null &&
    "type" in value &&
    (value as unknown as { type: unknown }).type === "peer-joined"
  );
}

function isPeerLeft(value: unknown): value is PeerLeftFrame {
  return (
    typeof value === "object" &&
    value !== null &&
    "type" in value &&
    (value as unknown as { type: unknown }).type === "peer-left"
  );
}

describe("signalingServer peer-discovery frames", () => {
  test("a lone newcomer receives peers-present with an empty list", async () => {
    const { url } = mountSignalingApp(pickPort());
    const alice = await openSignalingClient(url);

    alice.send({ type: "join", peerId: "peer-alice" });
    const first = await waitForMessage(alice);

    expect(isPeersPresent(first)).toBeTruthy();
    if (!isPeersPresent(first)) throw new Error("type narrowing");
    expect(first.peerIds).toEqual([]);

    alice.close();
  });

  test("a second joiner receives peers-present listing the incumbent", async () => {
    const { url } = mountSignalingApp(pickPort());
    const alice = await openSignalingClient(url);
    alice.send({ type: "join", peerId: "peer-alice" });
    await waitForMessage(alice); // drain alice's own peers-present

    const bob = await openSignalingClient(url);
    bob.send({ type: "join", peerId: "peer-bob" });

    const bobFirst = await waitForMessage(bob);
    expect(isPeersPresent(bobFirst)).toBeTruthy();
    if (!isPeersPresent(bobFirst)) throw new Error("type narrowing");
    expect(bobFirst.peerIds).toEqual(["peer-alice"]);

    alice.close();
    bob.close();
  });

  test("an incumbent receives peer-joined when a new peer joins", async () => {
    const { url } = mountSignalingApp(pickPort());
    const alice = await openSignalingClient(url);
    alice.send({ type: "join", peerId: "peer-alice" });
    await waitForMessage(alice); // drain alice's own peers-present

    const bob = await openSignalingClient(url);
    bob.send({ type: "join", peerId: "peer-bob" });

    const aliceNotif = await waitForMessage(alice);
    expect(isPeerJoined(aliceNotif)).toBeTruthy();
    if (!isPeerJoined(aliceNotif)) throw new Error("type narrowing");
    expect(aliceNotif.peerId).toBe("peer-bob");

    alice.close();
    bob.close();
  });

  test("a three-peer sequence delivers peers-present and peer-joined as expected", async () => {
    const { url } = mountSignalingApp(pickPort());

    const alice = await openSignalingClient(url);
    alice.send({ type: "join", peerId: "peer-alice" });
    const aliceFirst = await waitForMessage(alice);
    expect(isPeersPresent(aliceFirst)).toBeTruthy();
    if (!isPeersPresent(aliceFirst)) throw new Error("type narrowing");
    expect(aliceFirst.peerIds).toEqual([]);

    const bob = await openSignalingClient(url);
    bob.send({ type: "join", peerId: "peer-bob" });
    const bobFirst = await waitForMessage(bob);
    expect(isPeersPresent(bobFirst)).toBeTruthy();
    if (!isPeersPresent(bobFirst)) throw new Error("type narrowing");
    expect(bobFirst.peerIds).toEqual(["peer-alice"]);

    const aliceNotifForBob = await waitForMessage(alice);
    expect(isPeerJoined(aliceNotifForBob)).toBeTruthy();
    if (!isPeerJoined(aliceNotifForBob)) throw new Error("type narrowing");
    expect(aliceNotifForBob.peerId).toBe("peer-bob");

    const carol = await openSignalingClient(url);
    carol.send({ type: "join", peerId: "peer-carol" });
    const carolFirst = await waitForMessage(carol);
    expect(isPeersPresent(carolFirst)).toBeTruthy();
    if (!isPeersPresent(carolFirst)) throw new Error("type narrowing");
    expect(carolFirst.peerIds.sort()).toEqual(["peer-alice", "peer-bob"].sort());

    const aliceNotifForCarol = await waitForMessage(alice);
    expect(isPeerJoined(aliceNotifForCarol)).toBeTruthy();
    if (!isPeerJoined(aliceNotifForCarol)) throw new Error("type narrowing");
    expect(aliceNotifForCarol.peerId).toBe("peer-carol");

    const bobNotifForCarol = await waitForMessage(bob);
    expect(isPeerJoined(bobNotifForCarol)).toBeTruthy();
    if (!isPeerJoined(bobNotifForCarol)) throw new Error("type narrowing");
    expect(bobNotifForCarol.peerId).toBe("peer-carol");

    alice.close();
    bob.close();
    carol.close();
  });

  test("the newcomer never receives a peer-joined for its own id", async () => {
    const { url } = mountSignalingApp(pickPort());
    const dave = await openSignalingClient(url);
    dave.send({ type: "join", peerId: "peer-dave" });
    await waitForMessage(dave); // peers-present

    // Give the server time to process the join and emit any subsequent
    // frames. The test passes if nothing else arrives.
    await new Promise((r) => setTimeout(r, 150));
    const unexpected = dave.drain();
    expect(unexpected).toEqual([]);

    dave.close();
  });

  test("incumbents receive peer-left when a joined peer closes its socket", async () => {
    const { url } = mountSignalingApp(pickPort());
    const alice = await openSignalingClient(url);
    alice.send({ type: "join", peerId: "peer-alice" });
    await waitForMessage(alice); // peers-present

    const bob = await openSignalingClient(url);
    bob.send({ type: "join", peerId: "peer-bob" });
    await waitForMessage(bob); // peers-present
    await waitForMessage(alice); // peer-joined bob

    bob.close();

    const aliceNotif = await waitForMessage(alice, 2000);
    expect(isPeerLeft(aliceNotif)).toBeTruthy();
    if (!isPeerLeft(aliceNotif)) throw new Error("type narrowing");
    expect(aliceNotif.peerId).toBe("peer-bob");

    alice.close();
  });

  test("a peer that never joined does not trigger peer-left on close", async () => {
    const { url } = mountSignalingApp(pickPort());
    const alice = await openSignalingClient(url);
    alice.send({ type: "join", peerId: "peer-alice" });
    await waitForMessage(alice); // peers-present

    // A bystander connects but never sends `join`. On close, no peer-left
    // should go to Alice because the bystander was never a joined peer.
    const bystander = await openSignalingClient(url);
    bystander.close();

    await new Promise((r) => setTimeout(r, 150));
    expect(alice.drain()).toEqual([]);

    alice.close();
  });

  test("the existing relay/error contract is unchanged under the extended protocol", async () => {
    const { url } = mountSignalingApp(pickPort());
    const eve = await openSignalingClient(url);
    eve.send({ type: "join", peerId: "peer-eve" });
    await waitForMessage(eve); // peers-present

    eve.send({
      type: "signal",
      peerId: "peer-eve",
      targetPeerId: "peer-nobody",
      payload: { ice: "candidate" },
    });

    const reply = (await waitForMessage(eve)) as unknown as { type: string; reason: string };
    expect(reply.type).toBe("error");
    expect(reply.reason).toBe("unknown-target");

    eve.close();
  });
});
