/**
 * Adapter-level tests for the fragment receive internals in
 * mesh-webrtc-adapter: the per-chunk accounting inside
 * {@link handleSyncFragment} (chunksReceived/bytesReceived stamps, the
 * create-once `inFlightSync` guard, the sync-vs-async reassembly dispatch),
 * and the {@link dispatchReassembled} fork that routes a reassembled blob
 * to `onBlobMessage` and swallows a malformed reassembly.
 *
 * The per-chunk counters are observed through the `sync-progress` event the
 * adapter emits on every fragment, so the assertions read the real wire-side
 * signal rather than reaching into slot internals. Everything is driven
 * through the data channel's `onmessage` against a fake RTCPeerConnection.
 */

import { describe, expect, test } from "bun:test";
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
  sent: Uint8Array[] = [];

  open(): void {
    this.readyState = "open";
    this.onopen?.();
  }
  send(bytes: Uint8Array<ArrayBuffer>): void {
    this.sent.push(new Uint8Array(bytes));
  }
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

interface SyncProgress {
  kind: string;
  chunksReceived: number;
  bytesReceived: number;
}

function build(opts: { syncYieldEnabled?: boolean } = {}): {
  adapter: MeshWebRTCAdapter;
  channel: FakeDataChannel;
  slot: () => { inFlightSync?: unknown };
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
  channel.open();
  const slot = () =>
    (adapter as unknown as { slots: Map<string, { inFlightSync?: unknown }> }).slots.get(
      REMOTE
    ) as { inFlightSync?: unknown };
  return { adapter, channel, slot };
}

function serialise(adapter: MeshWebRTCAdapter, m: Message): Uint8Array<ArrayBuffer> {
  return (
    adapter as unknown as { serialiseMessage(m: Message): Uint8Array<ArrayBuffer> }
  ).serialiseMessage(m);
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

/** Build a length-prefixed wire frame: [uint32 headerLen][header][data]. */
function wireFrame(header: Record<string, unknown>, data: Uint8Array): Uint8Array<ArrayBuffer> {
  const headerBytes = new TextEncoder().encode(JSON.stringify(header));
  const out = new Uint8Array(4 + headerBytes.length + data.length);
  new DataView(out.buffer).setUint32(0, headerBytes.length, false);
  out.set(headerBytes, 4);
  out.set(data, 4 + headerBytes.length);
  return out as Uint8Array<ArrayBuffer>;
}

/** Fragment arbitrary bytes into exactly `count` ordered sync-fragments. */
function fragment(bytes: Uint8Array, id: string, count: number): Uint8Array<ArrayBuffer>[] {
  const chunkSize = Math.max(1, Math.ceil(bytes.length / count));
  const frags = chunkSyncMessage(bytes, id, chunkSize);
  if (frags.length !== count) {
    throw new Error(`expected ${count} fragments, got ${frags.length}`);
  }
  return frags;
}

const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 0));

describe("handleSyncFragment per-chunk accounting", () => {
  test("emits a fragment-received beat with a running chunk/byte count", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const progress: SyncProgress[] = [];
    // `sync-progress` is polly-specific, outside Automerge's typed event map
    // (production emits it via the same cast); subscribe through the cast.
    (adapter as unknown as { on(ev: string, cb: (e: SyncProgress) => void): void }).on(
      "sync-progress",
      (e) => progress.push(e)
    );
    const wire = serialise(adapter, makeMessage({ data: new Uint8Array(60) }));
    const frags = fragment(wire, "msg-A", 3);
    channel.deliver(frags[0] as Uint8Array);
    const first = progress.at(-1);
    if (!first) throw new Error("no progress beat after first chunk");
    expect(first.kind).toBe("fragment-received");
    expect(first.chunksReceived).toBe(1);
    expect(first.bytesReceived).toBeGreaterThan(0);
  });

  test("accumulates the chunk count across chunks rather than resetting inFlightSync", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const progress: SyncProgress[] = [];
    // `sync-progress` is polly-specific, outside Automerge's typed event map
    // (production emits it via the same cast); subscribe through the cast.
    (adapter as unknown as { on(ev: string, cb: (e: SyncProgress) => void): void }).on(
      "sync-progress",
      (e) => progress.push(e)
    );
    const wire = serialise(adapter, makeMessage({ data: new Uint8Array(60) }));
    const frags = fragment(wire, "msg-A", 3);
    channel.deliver(frags[0] as Uint8Array);
    const afterFirst = progress.at(-1)?.bytesReceived ?? 0;
    channel.deliver(frags[1] as Uint8Array);
    const second = progress.at(-1);
    if (!second) throw new Error("no progress beat after second chunk");
    // The create-once guard must keep the same inFlightSync, so the second
    // chunk's count is 2 and its byte total strictly exceeds the first.
    expect(second.chunksReceived).toBe(2);
    expect(second.bytesReceived).toBeGreaterThan(afterFirst);
  });

  test("defers the reassembled dispatch to a macrotask under the yield path", async () => {
    const { adapter, channel } = build({ syncYieldEnabled: true });
    const messages: Message[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    const wire = serialise(adapter, makeMessage());
    const frags = fragment(wire, "msg-async", 2);
    channel.deliver(frags[0] as Uint8Array);
    channel.deliver(frags[1] as Uint8Array);
    // The reassembly itself is on a macrotask, so after a single flush the
    // dispatch has only just started and the emit is still pending — a
    // synchronous reassembly would have surfaced the message by now.
    await flush();
    expect(messages).toHaveLength(0);
    await flush();
    expect(messages).toHaveLength(1);
  });
});

describe("dispatchReassembled routing", () => {
  test("routes a reassembled blob message to onBlobMessage with intact header and data", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    const blobCalls: Array<{ header: Record<string, unknown>; data: Uint8Array }> = [];
    adapter.on("message", (m: Message) => messages.push(m));
    adapter.onBlobMessage = (_peer, header, data) => blobCalls.push({ header, data });
    const payload = new Uint8Array([10, 20, 30, 40, 50]);
    const blobWire = wireFrame({ type: "blob-chunk", blobId: "b1", seq: 7 }, payload);
    const frags = fragment(blobWire, "blob-msg", 2);
    channel.deliver(frags[0] as Uint8Array);
    channel.deliver(frags[1] as Uint8Array);
    expect(messages).toHaveLength(0);
    expect(blobCalls).toHaveLength(1);
    expect(blobCalls[0]?.header.type).toBe("blob-chunk");
    expect(blobCalls[0]?.header.seq).toBe(7);
    expect(Array.from(blobCalls[0]?.data as Uint8Array)).toEqual([10, 20, 30, 40, 50]);
  });

  test("a reassembled ordinary message is not diverted to a registered blob handler", () => {
    const { adapter, channel } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    const blobCalls: unknown[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    adapter.onBlobMessage = (...args) => blobCalls.push(args);
    // onBlobMessage is registered, but the reassembled payload is an
    // ordinary sync message — the blob fork is gated on the message type,
    // not merely on a handler being present, so it must emit upward.
    const wire = serialise(adapter, makeMessage({ data: new Uint8Array(50) }));
    const frags = fragment(wire, "normal-msg", 2);
    channel.deliver(frags[0] as Uint8Array);
    channel.deliver(frags[1] as Uint8Array);
    expect(messages).toHaveLength(1);
    expect(blobCalls).toHaveLength(0);
  });

  test("swallows a malformed reassembly and tears down the in-flight state without throwing", () => {
    const { adapter, channel, slot } = build({ syncYieldEnabled: false });
    const messages: Message[] = [];
    adapter.on("message", (m: Message) => messages.push(m));
    // A header-length prefix that overruns the buffer makes deserialiseMessage
    // throw; the dispatch must catch it, emit nothing, and still clear the
    // reassembly bookkeeping so the slot is not left wedged.
    const garbage = new Uint8Array([0xff, 0xff, 0xff, 0xff, 1, 2, 3, 4, 5, 6]);
    const frags = fragment(garbage, "bad-msg", 2);
    expect(() => {
      channel.deliver(frags[0] as Uint8Array);
      channel.deliver(frags[1] as Uint8Array);
    }).not.toThrow();
    expect(messages).toHaveLength(0);
    expect(slot().inFlightSync).toBeUndefined();
  });
});

describe("handleSyncFragment defensive guards", () => {
  test("ignores a fragment for a peer with no slot", () => {
    const { adapter } = build({ syncYieldEnabled: false });
    const wire = serialise(adapter, makeMessage());
    const frag = fragment(wire, "ghost", 1)[0] as Uint8Array;
    expect(() =>
      (
        adapter as unknown as { handleSyncFragment(id: string, b: Uint8Array): void }
      ).handleSyncFragment("ghost-peer", frag)
    ).not.toThrow();
  });

  test("ignores bytes that look like a fragment but fail to parse", () => {
    const { adapter } = build({ syncYieldEnabled: false });
    // Header contains the sync-fragment marker (so the cheap probe passes)
    // but is truncated JSON, so the full parse returns undefined.
    const badHeader = '{"type":"sync-fragment"';
    const headerBytes = new TextEncoder().encode(badHeader);
    const frame = new Uint8Array(4 + headerBytes.length);
    new DataView(frame.buffer).setUint32(0, headerBytes.length, false);
    frame.set(headerBytes, 4);
    expect(() =>
      (
        adapter as unknown as { handleSyncFragment(id: string, b: Uint8Array): void }
      ).handleSyncFragment(REMOTE, frame)
    ).not.toThrow();
  });
});
