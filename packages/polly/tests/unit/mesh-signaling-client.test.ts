/**
 * Unit tests for MeshSignalingClient.
 *
 * The module's prose calls it browser-only and "cannot be exercised under
 * bun:test" — but the constructor accepts an injectable `WebSocket`, which
 * lets a controllable fake stand in for the real socket. These tests drive
 * the join handshake, frame routing, the send paths, and the reconnect
 * backoff entirely in-process.
 */
import { afterEach, describe, expect, test } from "bun:test";
import { type CustomSignalingFrame, MeshSignalingClient } from "@/shared/lib/mesh-signaling-client";

/** A controllable WebSocket double. Records what the client sends and lets
 * the test fire the lifecycle/message events the client listens for. */
class FakeWebSocket {
  static readonly CONNECTING = 0;
  static readonly OPEN = 1;
  static readonly CLOSED = 3;
  static instances: FakeWebSocket[] = [];
  static last(): FakeWebSocket {
    const ws = FakeWebSocket.instances.at(-1);
    if (!ws) throw new Error("no FakeWebSocket has been constructed");
    return ws;
  }

  readonly url: string;
  readyState: number = FakeWebSocket.CONNECTING;
  readonly sent: string[] = [];
  closeCalls = 0;
  private readonly listeners = new Map<string, Array<(ev: unknown) => void>>();

  constructor(url: string) {
    this.url = url;
    FakeWebSocket.instances.push(this);
  }

  addEventListener(type: string, fn: (ev: unknown) => void): void {
    const list = this.listeners.get(type) ?? [];
    list.push(fn);
    this.listeners.set(type, list);
  }

  send(data: string): void {
    this.sent.push(data);
  }

  close(): void {
    this.closeCalls += 1;
    this.readyState = FakeWebSocket.CLOSED;
    this.emit("close", {});
  }

  // --- test controls ---
  emit(type: string, ev: unknown): void {
    for (const fn of this.listeners.get(type) ?? []) fn(ev);
  }
  fireOpen(): void {
    this.readyState = FakeWebSocket.OPEN;
    this.emit("open", {});
  }
  fireMessage(data: unknown): void {
    this.emit("message", { data });
  }
  fireError(err: unknown): void {
    this.emit("error", err);
  }
  lastSent(): Record<string, unknown> {
    const raw = this.sent.at(-1);
    if (raw === undefined) throw new Error("nothing was sent");
    return JSON.parse(raw);
  }
}

const WS = FakeWebSocket as unknown as typeof WebSocket;

interface Captured {
  signals: Array<{ from: string; payload: unknown }>;
  errors: Array<{ reason: string; target?: string }>;
  opens: number;
  closes: number;
  peersPresent: string[][];
  joined: string[];
  left: string[];
  custom: CustomSignalingFrame[];
}

function makeClient(extra: Record<string, unknown> = {}): {
  client: MeshSignalingClient;
  cap: Captured;
} {
  const cap: Captured = {
    signals: [],
    errors: [],
    opens: 0,
    closes: 0,
    peersPresent: [],
    joined: [],
    left: [],
    custom: [],
  };
  const client = new MeshSignalingClient({
    url: "ws://localhost:9/sig",
    peerId: "local-peer",
    onSignal: (from, payload) => cap.signals.push({ from, payload }),
    onError: (reason, target) => cap.errors.push({ reason, target }),
    onOpen: () => {
      cap.opens += 1;
    },
    onClose: () => {
      cap.closes += 1;
    },
    onPeersPresent: (ids) => cap.peersPresent.push(ids),
    onPeerJoined: (id) => cap.joined.push(id),
    onPeerLeft: (id) => cap.left.push(id),
    onCustomFrame: (frame) => cap.custom.push(frame),
    WebSocket: WS,
    ...extra,
  });
  return { client, cap };
}

/** Construct, connect, and complete the open handshake. Returns the live socket. */
async function connectClient(extra?: Record<string, unknown>): Promise<{
  client: MeshSignalingClient;
  cap: Captured;
  ws: FakeWebSocket;
}> {
  const { client, cap } = makeClient(extra);
  const connected = client.connect();
  const ws = FakeWebSocket.last();
  ws.fireOpen();
  await connected;
  return { client, cap, ws };
}

afterEach(() => {
  FakeWebSocket.instances.length = 0;
});

describe("MeshSignalingClient — construction", () => {
  test("throws when no WebSocket implementation is available", () => {
    const saved = globalThis.WebSocket;
    try {
      // @ts-expect-error — removing the global to exercise the guard
      globalThis.WebSocket = undefined;
      expect(
        () =>
          new MeshSignalingClient({
            url: "ws://x",
            peerId: "p",
            onSignal: () => {},
          })
      ).toThrow(/no WebSocket implementation/);
    } finally {
      globalThis.WebSocket = saved;
    }
  });

  test("uses the injected WebSocket constructor over the global", () => {
    const { client } = makeClient();
    expect(client.url).toBe("ws://localhost:9/sig");
    expect(client.peerId).toBe("local-peer");
    expect(client.isConnected).toBe(false);
  });
});

describe("MeshSignalingClient — connect handshake", () => {
  test("sends a join frame and resolves on open", async () => {
    const { cap, ws } = await connectClient();
    expect(ws.lastSent()).toEqual({ type: "join", peerId: "local-peer" });
    expect(cap.opens).toBe(1);
    expect(ws.readyState).toBe(FakeWebSocket.OPEN);
  });

  test("reports connected only after the handshake", async () => {
    const { client } = makeClient();
    const connected = client.connect();
    const ws = FakeWebSocket.last();
    expect(client.isConnected).toBe(false);
    ws.fireOpen();
    await connected;
    expect(client.isConnected).toBe(true);
  });

  test("rejects when the socket errors before opening", async () => {
    const { client } = makeClient();
    const connected = client.connect();
    FakeWebSocket.last().fireError(new Error("connect refused"));
    await expect(connected).rejects.toThrow("connect refused");
  });

  test("a post-open error does not reject the already-resolved connect", async () => {
    const { ws } = await connectClient();
    // Must not throw or reject anything; the connect promise already settled.
    expect(() => ws.fireError(new Error("late"))).not.toThrow();
  });
});

describe("MeshSignalingClient — incoming frame routing", () => {
  test("routes a signal frame to onSignal with sender and payload", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "signal", peerId: "remote", payload: { sdp: "x" } }));
    expect(cap.signals).toEqual([{ from: "remote", payload: { sdp: "x" } }]);
  });

  test("drops a signal frame whose peerId is not a string", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "signal", peerId: 42, payload: "p" }));
    expect(cap.signals).toEqual([]);
  });

  test("routes peers-present with the peer-id array", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "peers-present", peerIds: ["a", "b"] }));
    expect(cap.peersPresent).toEqual([["a", "b"]]);
  });

  test("drops peers-present whose peerIds is not an array", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "peers-present", peerIds: "a" }));
    expect(cap.peersPresent).toEqual([]);
  });

  test("routes peer-joined and peer-left to their callbacks", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "peer-joined", peerId: "newbie" }));
    ws.fireMessage(JSON.stringify({ type: "peer-left", peerId: "newbie" }));
    expect(cap.joined).toEqual(["newbie"]);
    expect(cap.left).toEqual(["newbie"]);
  });

  test("drops peer-joined / peer-left without a string peerId", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "peer-joined" }));
    ws.fireMessage(JSON.stringify({ type: "peer-left", peerId: 1 }));
    expect(cap.joined).toEqual([]);
    expect(cap.left).toEqual([]);
  });

  test("routes an error frame with reason and target", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(
      JSON.stringify({ type: "error", reason: "unknown-target", targetPeerId: "ghost" })
    );
    expect(cap.errors).toEqual([{ reason: "unknown-target", target: "ghost" }]);
  });

  test("error frame omits a non-string targetPeerId", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "error", reason: "malformed", targetPeerId: 7 }));
    expect(cap.errors).toEqual([{ reason: "malformed", target: undefined }]);
  });

  test("drops an error frame without a string reason", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "error", targetPeerId: "ghost" }));
    expect(cap.errors).toEqual([]);
  });

  test("routes an unknown frame type to onCustomFrame", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ type: "pairing-return", token: "abc" }));
    expect(cap.custom).toEqual([{ type: "pairing-return", token: "abc" }]);
  });

  test("parses a non-string frame body directly (no JSON.parse)", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage({ type: "signal", peerId: "obj", payload: 1 });
    expect(cap.signals).toEqual([{ from: "obj", payload: 1 }]);
  });
});

describe("MeshSignalingClient — malformed frames are dropped", () => {
  test("drops invalid JSON", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage("{not json");
    expect(cap.signals).toEqual([]);
    expect(cap.custom).toEqual([]);
  });

  test("drops a non-object payload", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify(123));
    ws.fireMessage(JSON.stringify(null));
    expect(cap.custom).toEqual([]);
  });

  test("drops a frame with no string type", async () => {
    const { cap, ws } = await connectClient();
    ws.fireMessage(JSON.stringify({ peerId: "remote", payload: "p" }));
    ws.fireMessage(JSON.stringify({ type: 9 }));
    expect(cap.signals).toEqual([]);
    expect(cap.custom).toEqual([]);
  });
});

describe("MeshSignalingClient — sendSignal", () => {
  test("sends a signal frame and returns true when open", async () => {
    const { client, ws } = await connectClient();
    const ok = client.sendSignal("remote", { ice: "cand" });
    expect(ok).toBe(true);
    expect(ws.lastSent()).toEqual({
      type: "signal",
      peerId: "local-peer",
      targetPeerId: "remote",
      payload: { ice: "cand" },
    });
  });

  test("returns false before the handshake completes", () => {
    const { client } = makeClient();
    client.connect();
    expect(client.sendSignal("remote", "x")).toBe(false);
  });

  test("returns false when the socket is not in the OPEN readyState", async () => {
    const { client, ws } = await connectClient();
    ws.readyState = FakeWebSocket.CLOSED;
    expect(client.sendSignal("remote", "x")).toBe(false);
  });

  test("returns false after close", async () => {
    const { client } = await connectClient();
    client.close();
    expect(client.sendSignal("remote", "x")).toBe(false);
  });
});

describe("MeshSignalingClient — sendCustom", () => {
  test("sends { ...payload, type } and returns true when open", async () => {
    const { client, ws } = await connectClient();
    const ok = client.sendCustom("pairing-return", { token: "t", to: "issuer" });
    expect(ok).toBe(true);
    expect(ws.lastSent()).toEqual({ token: "t", to: "issuer", type: "pairing-return" });
  });

  test("type wins over a type field in the payload", async () => {
    const { client, ws } = await connectClient();
    client.sendCustom("real-type", { type: "spoofed" } as Record<string, unknown>);
    expect(ws.lastSent().type).toBe("real-type");
  });

  test("defaults the payload to an empty object", async () => {
    const { client, ws } = await connectClient();
    expect(client.sendCustom("ping")).toBe(true);
    expect(ws.lastSent()).toEqual({ type: "ping" });
  });

  test("returns false when not connected", () => {
    const { client } = makeClient();
    expect(client.sendCustom("ping")).toBe(false);
  });
});

describe("MeshSignalingClient — optional callbacks may be omitted", () => {
  // Every lifecycle/routing callback except onSignal is optional. With them
  // omitted, the client must invoke them via `?.` and never throw — these
  // assertions pin that the optional-chaining guards are load-bearing.
  function bareClient(): MeshSignalingClient {
    return new MeshSignalingClient({
      url: "ws://localhost:9/sig",
      peerId: "local-peer",
      onSignal: () => {},
      WebSocket: WS,
    });
  }

  test("connect and open do not require onOpen", async () => {
    const client = bareClient();
    const connected = client.connect();
    FakeWebSocket.last().fireOpen();
    await expect(connected).resolves.toBeUndefined();
  });

  test("every built-in frame is tolerated without its callback", async () => {
    const client = bareClient();
    const connected = client.connect();
    const ws = FakeWebSocket.last();
    ws.fireOpen();
    await connected;
    expect(() => {
      ws.fireMessage(JSON.stringify({ type: "peers-present", peerIds: ["a"] }));
      ws.fireMessage(JSON.stringify({ type: "peer-joined", peerId: "a" }));
      ws.fireMessage(JSON.stringify({ type: "peer-left", peerId: "a" }));
      ws.fireMessage(JSON.stringify({ type: "error", reason: "malformed" }));
      ws.fireMessage(JSON.stringify({ type: "custom-thing", x: 1 }));
    }).not.toThrow();
  });

  test("close does not require onClose", async () => {
    const client = bareClient();
    const connected = client.connect();
    FakeWebSocket.last().fireOpen();
    await connected;
    expect(() => client.close()).not.toThrow();
  });
});

describe("MeshSignalingClient — close", () => {
  test("closes the socket and reports disconnected", async () => {
    const { client, cap, ws } = await connectClient();
    client.close();
    expect(ws.closeCalls).toBe(1);
    expect(client.isConnected).toBe(false);
    expect(cap.closes).toBe(1);
  });
});

describe("MeshSignalingClient — reconnect backoff", () => {
  // The reconnect loop schedules through the global setTimeout. Capture the
  // scheduled callbacks so the test can inspect the delay and drive them by
  // hand, without waiting on real timers.
  const realSetTimeout = globalThis.setTimeout;
  const realClearTimeout = globalThis.clearTimeout;
  let scheduled: Array<{ fn: () => void; delay: number }>;

  function installFakeTimers(): void {
    scheduled = [];
    globalThis.setTimeout = ((fn: () => void, delay?: number) => {
      scheduled.push({ fn, delay: delay ?? 0 });
      return scheduled.length as unknown as ReturnType<typeof setTimeout>;
    }) as typeof setTimeout;
    globalThis.clearTimeout = (() => {}) as typeof clearTimeout;
  }

  afterEach(() => {
    globalThis.setTimeout = realSetTimeout;
    globalThis.clearTimeout = realClearTimeout;
    FakeWebSocket.instances.length = 0;
  });

  test("schedules a reconnect at the base delay after an open connection drops", async () => {
    installFakeTimers();
    const { ws } = await connectClient();
    ws.close();
    expect(scheduled).toHaveLength(1);
    expect(scheduled[0]?.delay).toBe(250);
  });

  test("a dropped reconnect attempt backs off to twice the base delay", async () => {
    installFakeTimers();
    const { ws } = await connectClient();
    const before = FakeWebSocket.instances.length;
    ws.close();
    // Fire the first reconnect timer: it opens a new socket via connect().
    scheduled[0]?.fn();
    expect(FakeWebSocket.instances.length).toBe(before + 1);
    // That reconnect's socket errors before opening → connect() rejects →
    // the next attempt is scheduled at base * 2 ** 1.
    FakeWebSocket.last().fireError(new Error("still down"));
    // Let the rejected connect() promise propagate through its async wrapper
    // and into the .catch that schedules the next attempt.
    for (let i = 0; i < 8; i++) await Promise.resolve();
    expect(scheduled.at(-1)?.delay).toBe(500);
  });

  test("close cancels a pending reconnect", async () => {
    installFakeTimers();
    const { client, ws } = await connectClient();
    ws.close();
    const before = FakeWebSocket.instances.length;
    client.close();
    // The scheduled callback must no-op now that the client is stopping.
    scheduled[0]?.fn();
    expect(FakeWebSocket.instances.length).toBe(before);
  });

  test("does not reconnect when the socket closes before it ever opened", async () => {
    installFakeTimers();
    const { client } = makeClient();
    client.connect();
    const ws = FakeWebSocket.last();
    ws.close(); // close preempts open → wasOpen is false
    expect(scheduled).toHaveLength(0);
  });
});
