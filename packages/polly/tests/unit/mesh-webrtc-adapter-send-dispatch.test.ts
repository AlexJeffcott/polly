/**
 * Adapter-level tests for the send/dispatch transcript island in
 * mesh-webrtc-adapter: the outbound `send` queue + per-handle wire
 * transcript (polly#107), the `dispatchMessage` routing fork
 * (sync-fragment / blob / ordinary / malformed), the sync-vs-async emit
 * scheduling (polly#104), and the `inFlightSync` reassembly bookkeeping
 * that `finishInFlightSyncApply` tears down.
 *
 * Everything is driven through the public surface — `send`, the data
 * channel's `onmessage`, and `handlePeerJoined` — against a hand-rolled
 * fake RTCPeerConnection so the suite sits on bun:test with no real WebRTC.
 * `syncYieldEnabled: false` is used wherever a test needs the dispatch
 * chain to run synchronously so the reassembly state can be asserted
 * without chasing macrotasks.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import type { Message } from "@automerge/automerge-repo/slim";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";
import { chunkSyncMessage } from "@/shared/lib/sync-fragment";

function createSignalingStub(peerId: string): MeshSignalingClient {
  const options: MeshSignalingClientOptions = {
    url: "ws://stub",
    peerId,
    onSignal: () => {},
  };
  return {
    url: options.url,
    peerId,
    isConnected: true,
    sendSignal: (): boolean => true,
    connect: async (): Promise<void> => {},
    close: (): void => {},
  } as unknown as MeshSignalingClient;
}

class FakeDataChannel {
  onopen: (() => void) | null = null;
  onmessage: ((ev: { data: ArrayBuffer | Uint8Array }) => void) | null = null;
  onclose: (() => void) | null = null;
  onerror: ((ev: unknown) => void) | null = null;
  readyState: "connecting" | "open" | "closed" = "connecting";
  bufferedAmount = 0;
  sent: Uint8Array[] = [];

  open(): void {
    this.readyState = "open";
    this.onopen?.();
  }
  send(bytes: Uint8Array<ArrayBuffer>): void {
    this.sent.push(new Uint8Array(bytes));
  }
  /** Push wire bytes through the receive path exactly as the live
   * WebRTC stack does — as a fresh ArrayBuffer. */
  deliver(bytes: Uint8Array): void {
    const copy = new Uint8Array(bytes.length);
    copy.set(bytes);
    this.onmessage?.({ data: copy.buffer });
  }
  close(): void {
    this.readyState = "closed";
    this.onclose?.();
  }
}

class FakePeerConnection {
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  channel?: FakeDataChannel;

  createDataChannel(_label: string, _options: unknown): FakeDataChannel {
    this.channel = new FakeDataChannel();
    return this.channel;
  }
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    return { type: "offer", sdp: "v=0\r\nfake\r\n" };
  }
  async setLocalDescription(_d: RTCSessionDescriptionInit): Promise<void> {}
  async setRemoteDescription(_d: RTCSessionDescriptionInit): Promise<void> {}
  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: "answer", sdp: "v=0\r\nfake\r\n" };
  }
  async addIceCandidate(_c: unknown): Promise<void> {}
  close(): void {
    this.connectionState = "closed";
    this.onconnectionstatechange?.();
  }
}

const LOCAL = "peer-z";
const REMOTE = "peer-a";

interface SlotView {
  channel?: FakeDataChannel;
  pendingSends: Uint8Array[];
  pendingFragments: Map<string, unknown>;
  inFlightSync?: unknown;
  handles: Map<
    string,
    {
      lastSyncMessageOutAt?: number;
      lastSyncMessageOutSize?: number;
      lastSyncMessageOutType?: string;
      lastSyncMessageInAt?: number;
    }
  >;
  lastSyncHandshakeAttempt: {
    firstOutboundSendAt?: number;
    firstInboundMessageAt?: number;
  };
}

function build(opts: { syncYieldEnabled?: boolean; open?: boolean } = {}): {
  adapter: MeshWebRTCAdapter;
  channel: FakeDataChannel;
  slot: () => SlotView;
} {
  const pcs: FakePeerConnection[] = [];
  class CapturingPC extends FakePeerConnection {
    constructor() {
      super();
      pcs.push(this);
    }
  }
  const adapter = new MeshWebRTCAdapter({
    signaling: createSignalingStub(LOCAL),
    peerId: LOCAL,
    knownPeerIds: [REMOTE],
    syncYieldEnabled: opts.syncYieldEnabled,
    RTCPeerConnection: CapturingPC as unknown as typeof RTCPeerConnection,
  });
  adapter.handlePeerJoined(REMOTE);
  const channel = pcs[0]?.channel;
  if (!channel) throw new Error("test setup: no data channel created");
  if (opts.open !== false) channel.open();
  const slot = () =>
    (adapter as unknown as { slots: Map<string, SlotView> }).slots.get(REMOTE) as SlotView;
  return { adapter, channel, slot };
}

function makeMessage(over: Partial<Record<string, unknown>> = {}): Message {
  return {
    type: "sync",
    senderId: LOCAL,
    targetId: REMOTE,
    documentId: "doc-1",
    data: new Uint8Array([1, 2, 3, 4]),
    ...over,
  } as unknown as Message;
}

const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 0));

beforeEach(() => {
  // Each build() constructs its own adapter; nothing global to reset.
});

describe("MeshWebRTCAdapter.send outbound path", () => {
  test("sends immediately on an open channel", () => {
    const { adapter, channel } = build({ open: true });
    adapter.send(makeMessage());
    expect(channel.sent).toHaveLength(1);
  });

  test("queues into pendingSends while the channel is still connecting", () => {
    const { adapter, channel, slot } = build({ open: false });
    adapter.send(makeMessage());
    expect(channel.sent).toHaveLength(0);
    expect(slot().pendingSends).toHaveLength(1);
  });

  test("flushes queued sends when the channel finally opens", () => {
    const { adapter, channel, slot } = build({ open: false });
    adapter.send(makeMessage());
    adapter.send(makeMessage());
    expect(channel.sent).toHaveLength(0);
    channel.open();
    expect(channel.sent).toHaveLength(2);
    expect(slot().pendingSends).toHaveLength(0);
  });

  test("stamps firstOutboundSendAt once and leaves it fixed across later sends", () => {
    const { adapter, slot } = build({ open: true });
    adapter.send(makeMessage());
    const first = slot().lastSyncHandshakeAttempt.firstOutboundSendAt;
    expect(first).toBeGreaterThan(0);
    adapter.send(makeMessage());
    expect(slot().lastSyncHandshakeAttempt.firstOutboundSendAt).toBe(first);
  });

  test("records the per-handle outbound transcript when the message carries a documentId", () => {
    const { adapter, slot } = build({ open: true });
    adapter.send(makeMessage({ documentId: "doc-xyz", type: "sync" }));
    const entry = slot().handles.get("doc-xyz");
    if (!entry) throw new Error("no handle transcript entry recorded");
    expect(entry.lastSyncMessageOutType).toBe("sync");
    expect(entry.lastSyncMessageOutSize).toBeGreaterThan(0);
    expect(entry.lastSyncMessageOutAt).toBeGreaterThan(0);
  });

  test("does not create a handle transcript entry for a message without a documentId", () => {
    const { adapter, slot } = build({ open: true });
    adapter.send(makeMessage({ documentId: undefined }));
    expect(slot().handles.size).toBe(0);
  });

  test("creates an initiating slot when send targets a peer with no slot yet", () => {
    const { adapter } = build({ open: true });
    const slots = (adapter as unknown as { slots: Map<string, unknown> }).slots;
    slots.delete(REMOTE);
    expect(slots.has(REMOTE)).toBe(false);
    adapter.send(makeMessage());
    expect(slots.has(REMOTE)).toBe(true);
  });
});

describe("MeshWebRTCAdapter.dispatchMessage routing", () => {
  test("deserialises an ordinary message and emits it upward", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const received: Message[] = [];
    adapter.on("message", (m: Message) => received.push(m));
    const wire = (
      adapter as unknown as { serialiseMessage(m: Message): Uint8Array }
    ).serialiseMessage(makeMessage({ data: new Uint8Array([9, 8, 7]) }));
    channel.deliver(wire);
    expect(received).toHaveLength(1);
    expect(Array.from(received[0]?.data as Uint8Array)).toEqual([9, 8, 7]);
  });

  test("routes a blob message to onBlobMessage instead of the message stream", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    const blobCalls: Array<{ header: Record<string, unknown>; data: Uint8Array }> = [];
    adapter.onBlobMessage = (_peer, header, data) => blobCalls.push({ header, data });
    const header = new TextEncoder().encode(JSON.stringify({ type: "blob-chunk", blobId: "b1" }));
    const payload = new Uint8Array([42, 43]);
    const wire = new Uint8Array(4 + header.length + payload.length);
    new DataView(wire.buffer).setUint32(0, header.length, false);
    wire.set(header, 4);
    wire.set(payload, 4 + header.length);
    channel.deliver(wire);
    expect(blobCalls).toHaveLength(1);
    expect(blobCalls[0]?.header.type).toBe("blob-chunk");
    expect(Array.from(blobCalls[0]?.data as Uint8Array)).toEqual([42, 43]);
    expect(messages).toHaveLength(0);
  });

  test("drops a malformed frame without throwing or emitting", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    // A 2-byte frame is too short for even the length prefix.
    expect(() => channel.deliver(new Uint8Array([1, 2]))).not.toThrow();
    expect(messages).toHaveLength(0);
  });

  test("ignores a non-binary data payload", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    // The live path only forwards ArrayBuffer/Uint8Array; a string is dropped.
    channel.onmessage?.({ data: "a string frame" as unknown as ArrayBuffer });
    expect(messages).toHaveLength(0);
  });

  test("an ordinary message is not diverted to the blob handler when one is registered", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    const blobCalls: unknown[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    adapter.onBlobMessage = (...args) => blobCalls.push(args);
    // A registered onBlobMessage must NOT capture non-blob traffic — the
    // blob fork is gated on the message type, not merely on a handler
    // being present.
    const wire = (
      adapter as unknown as { serialiseMessage(m: Message): Uint8Array }
    ).serialiseMessage(makeMessage());
    channel.deliver(wire);
    expect(messages).toHaveLength(1);
    expect(blobCalls).toHaveLength(0);
  });
});

describe("MeshWebRTCAdapter defensive guards on missing state", () => {
  // These stamp/finish helpers can be re-entered for a peer whose slot has
  // already been torn down (teardown races the in-flight dispatch chain).
  // Each must bail on the absent slot rather than dereferencing it.
  test("stampFirstInboundMessage is a no-op for an unknown peer", () => {
    const { adapter } = build({ open: true });
    expect(() =>
      (
        adapter as unknown as { stampFirstInboundMessage(id: string): void }
      ).stampFirstInboundMessage("ghost-peer")
    ).not.toThrow();
  });

  test("stampHandleInbound is a no-op for an unknown peer", () => {
    const { adapter } = build({ open: true });
    expect(() =>
      (
        adapter as unknown as { stampHandleInbound(id: string, m: Message): void }
      ).stampHandleInbound("ghost-peer", makeMessage({ documentId: "doc-ghost" }))
    ).not.toThrow();
  });

  test("finishInFlightSyncApply is a no-op for an unknown peer and for a slot with no in-flight sync", () => {
    const { adapter } = build({ open: true });
    const finish = (
      adapter as unknown as { finishInFlightSyncApply(id: string): void }
    ).finishInFlightSyncApply.bind(adapter);
    expect(() => finish("ghost-peer")).not.toThrow();
    // The live REMOTE slot exists but has never started a fragment reassembly.
    expect(() => finish(REMOTE)).not.toThrow();
  });
});

describe("MeshWebRTCAdapter emit scheduling (polly#104)", () => {
  test("emits synchronously when sync-yield is disabled", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    let emitted = false;
    adapter.on("message", () => {
      emitted = true;
    });
    const wire = (
      adapter as unknown as { serialiseMessage(m: Message): Uint8Array }
    ).serialiseMessage(makeMessage());
    channel.deliver(wire);
    // No macrotask awaited — the emit already ran.
    expect(emitted).toBe(true);
  });

  test("defers the emit to a macrotask when sync-yield is enabled", async () => {
    const { adapter, channel } = build({ syncYieldEnabled: true });
    let emitted = false;
    adapter.on("message", () => {
      emitted = true;
    });
    const wire = (
      adapter as unknown as { serialiseMessage(m: Message): Uint8Array }
    ).serialiseMessage(makeMessage());
    channel.deliver(wire);
    // The onmessage callback returned before the emit fired.
    expect(emitted).toBe(false);
    await flush();
    expect(emitted).toBe(true);
  });
});

describe("MeshWebRTCAdapter inbound transcript stamping", () => {
  function serialise(adapter: MeshWebRTCAdapter, m: Message): Uint8Array {
    return (adapter as unknown as { serialiseMessage(m: Message): Uint8Array }).serialiseMessage(m);
  }

  test("stamps first-inbound and per-handle inbound timestamps on receive", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    channel.deliver(serialise(adapter, makeMessage({ documentId: "doc-in" })));
    expect(slot().lastSyncHandshakeAttempt.firstInboundMessageAt).toBeGreaterThan(0);
    expect(slot().handles.get("doc-in")?.lastSyncMessageInAt).toBeGreaterThan(0);
  });

  test("stamps firstInboundMessageAt only once across repeated receives", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    channel.deliver(serialise(adapter, makeMessage()));
    const first = slot().lastSyncHandshakeAttempt.firstInboundMessageAt;
    expect(first).toBeGreaterThan(0);
    channel.deliver(serialise(adapter, makeMessage()));
    expect(slot().lastSyncHandshakeAttempt.firstInboundMessageAt).toBe(first);
  });

  test("does not record an inbound handle entry for a message without a documentId", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    channel.deliver(serialise(adapter, makeMessage({ documentId: undefined })));
    // The first-inbound stamp still fires; only the per-handle layer is skipped.
    expect(slot().lastSyncHandshakeAttempt.firstInboundMessageAt).toBeGreaterThan(0);
    expect(slot().handles.size).toBe(0);
  });

  test("reuses the existing handle entry so the outbound transcript survives an inbound stamp", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    // Outbound first: stamps lastSyncMessageOutAt on the doc-shared entry.
    adapter.send(makeMessage({ documentId: "doc-shared" }));
    const outAt = slot().handles.get("doc-shared")?.lastSyncMessageOutAt;
    expect(outAt).toBeGreaterThan(0);
    // Inbound for the same doc must update the same entry, not replace it.
    channel.deliver(serialise(adapter, makeMessage({ documentId: "doc-shared" })));
    const entry = slot().handles.get("doc-shared");
    expect(entry?.lastSyncMessageInAt).toBeGreaterThan(0);
    expect(entry?.lastSyncMessageOutAt).toBe(outAt);
  });
});

describe("MeshWebRTCAdapter inFlightSync reassembly bookkeeping", () => {
  /** Serialise a message and fragment it under a chosen id with a small
   * chunk size so a tiny payload still produces `count` fragments. */
  function fragmentsFor(
    adapter: MeshWebRTCAdapter,
    id: string,
    count: number
  ): Uint8Array<ArrayBuffer>[] {
    const wire = (
      adapter as unknown as { serialiseMessage(m: Message): Uint8Array }
    ).serialiseMessage(makeMessage({ documentId: id, data: new Uint8Array(count * 20) }));
    const chunkSize = Math.ceil(wire.length / count);
    const frags = chunkSyncMessage(wire, id, chunkSize);
    if (frags.length !== count) {
      throw new Error(`expected ${count} fragments, got ${frags.length}`);
    }
    return frags;
  }

  test("clears inFlightSync once a fragmented message fully reassembles", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    const progress: Array<{ kind: string }> = [];
    // `sync-progress` is polly-specific, outside Automerge's typed event map
    // (production emits it via the same cast); subscribe through the cast.
    (adapter as unknown as { on(ev: string, cb: (e: { kind: string }) => void): void }).on(
      "sync-progress",
      (e) => progress.push(e)
    );
    const frags = fragmentsFor(adapter, "msg-A", 2);
    channel.deliver(frags[0] as Uint8Array);
    // Mid-reassembly: the in-flight state exists.
    expect(slot().inFlightSync).toBeDefined();
    channel.deliver(frags[1] as Uint8Array);
    // Fully applied and no other fragments pending — state is torn down.
    expect(slot().inFlightSync).toBeUndefined();
    expect(slot().pendingFragments.size).toBe(0);
    // The apply emits a dispatch-applied progress beat (after the per-chunk
    // fragment-received ones).
    expect(progress.map((p) => p.kind)).toContain("dispatch-applied");
  });

  test("reassembles and emits through the async yield path then tears down inFlightSync", async () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: true });
    const messages: Message[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    const frags = fragmentsFor(adapter, "msg-async", 2);
    channel.deliver(frags[0] as Uint8Array);
    channel.deliver(frags[1] as Uint8Array);
    // The reassembled dispatch and the emit are both deferred to macrotasks,
    // so nothing has surfaced synchronously yet.
    expect(messages).toHaveLength(0);
    expect(slot().inFlightSync).toBeDefined();
    // Drain the reassembly setTimeout, then the emit + finish setTimeout.
    await flush();
    await flush();
    expect(messages).toHaveLength(1);
    expect(slot().inFlightSync).toBeUndefined();
  });

  test("keeps inFlightSync alive when another message still has pending fragments", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    const a = fragmentsFor(adapter, "msg-A", 2);
    const b = fragmentsFor(adapter, "msg-B", 2);
    // Interleave: start A, start B, then complete A. When A's apply
    // finishes, B still has one outstanding fragment, so the
    // `applyBacklog === 0 && pendingFragments.size === 0` guard must
    // keep inFlightSync alive rather than tearing it down early.
    channel.deliver(a[0] as Uint8Array);
    channel.deliver(b[0] as Uint8Array);
    channel.deliver(a[1] as Uint8Array);
    expect(slot().pendingFragments.size).toBe(1);
    expect(slot().inFlightSync).toBeDefined();
  });
});

describe("MeshWebRTCAdapter inbound frame type handling (polly#161)", () => {
  test("dispatches a frame delivered as a raw Uint8Array, not only an ArrayBuffer", () => {
    // The browser stack hands `onmessage` an ArrayBuffer (the `deliver`
    // helper's path); werift hands a Uint8Array. Drive the Uint8Array branch
    // directly so it is not left as covered-but-undetected theatre.
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const received: Message[] = [];
    adapter.on("message", (m: Message) => received.push(m));
    const wire = (
      adapter as unknown as { serialiseMessage(m: Message): Uint8Array }
    ).serialiseMessage(makeMessage({ data: new Uint8Array([5, 6, 7]) }));
    channel.onmessage?.({ data: wire });
    expect(received).toHaveLength(1);
    expect(Array.from(received[0]?.data as Uint8Array)).toEqual([5, 6, 7]);
  });
});

describe("MeshWebRTCAdapter data-channel onclose (polly#161)", () => {
  test("the current channel's onclose clears the slot's channel reference", () => {
    const { channel, slot } = build({ open: true });
    expect(slot().channel).toBe(channel);
    channel.close();
    expect(slot().channel).toBeUndefined();
  });

  test("a stale channel's onclose does not clear a newer channel", () => {
    // A signalling reconnect can swap in a fresh data channel while the old
    // one's close fires late. The guard must only null the slot's channel
    // when the closing channel is still the current one (polly#133 family).
    const { channel, slot } = build({ open: true });
    const fresh = new FakeDataChannel();
    slot().channel = fresh;
    channel.close();
    expect(slot().channel).toBe(fresh);
  });
});
