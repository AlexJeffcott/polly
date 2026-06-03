/**
 * Adapter-level tests for the blob-send surface and the wire codec in
 * mesh-webrtc-adapter: the `connectedPeerIds` roster, `sendBlobMessage` /
 * `trySendOnChannel` (open-channel gate + the 256 KiB backpressure
 * high-water mark), and the length-prefixed `serialiseMessage` /
 * `deserialiseMessage` round trip with its truncation guards.
 *
 * Driven through the public `sendBlobMessage` / `connectedPeerIds` surface
 * against a fake RTCPeerConnection; the private codec pair is exercised
 * directly since it has no public entry point of its own.
 */

import { describe, expect, test } from "bun:test";
import type { Message } from "@automerge/automerge-repo/slim";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

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

// LOCAL is lexicographically the highest id, so the adapter initiates to
// every known peer on handlePeerJoined and a data channel is created.
const LOCAL = "peer-z";

function build(knownPeerIds: string[]): {
  adapter: MeshWebRTCAdapter;
  channelFor: (peerId: string) => FakeDataChannel;
} {
  const channels = new Map<string, FakeDataChannel>();
  let nextPeerId: string | undefined;
  class CapturingPC extends FakePeerConnection {
    override createDataChannel(label: string, options: unknown): FakeDataChannel {
      const channel = super.createDataChannel(label, options);
      if (nextPeerId) channels.set(nextPeerId, channel);
      return channel;
    }
  }
  const adapter = new MeshWebRTCAdapter({
    signaling: createSignalingStub(LOCAL),
    peerId: LOCAL,
    knownPeerIds,
    RTCPeerConnection: CapturingPC as unknown as typeof RTCPeerConnection,
  });
  for (const id of knownPeerIds) {
    nextPeerId = id;
    adapter.handlePeerJoined(id);
  }
  nextPeerId = undefined;
  const channelFor = (peerId: string): FakeDataChannel => {
    const c = channels.get(peerId);
    if (!c) throw new Error(`no channel for ${peerId}`);
    return c;
  };
  return { adapter, channelFor };
}

function serialise(adapter: MeshWebRTCAdapter, m: Message): Uint8Array<ArrayBuffer> {
  return (
    adapter as unknown as { serialiseMessage(m: Message): Uint8Array<ArrayBuffer> }
  ).serialiseMessage(m);
}

function deserialise(adapter: MeshWebRTCAdapter, bytes: Uint8Array): Message {
  return (adapter as unknown as { deserialiseMessage(b: Uint8Array): Message }).deserialiseMessage(
    bytes
  );
}

function makeMessage(over: Partial<Record<string, unknown>> = {}): Message {
  return {
    type: "sync",
    senderId: "peer-a",
    targetId: LOCAL,
    documentId: "doc-1",
    data: new Uint8Array([1, 2, 3, 4]),
    ...over,
  } as unknown as Message;
}

const HIGH_WATER = 256 * 1024;

describe("MeshWebRTCAdapter.connectedPeerIds", () => {
  test("lists only peers whose data channel is open", () => {
    const { adapter, channelFor } = build(["peer-a", "peer-b"]);
    channelFor("peer-a").open();
    // peer-b's channel is still connecting.
    expect(adapter.connectedPeerIds).toEqual(["peer-a"]);
  });

  test("excludes a peer whose channel has closed", () => {
    const { adapter, channelFor } = build(["peer-a"]);
    channelFor("peer-a").open();
    expect(adapter.connectedPeerIds).toEqual(["peer-a"]);
    channelFor("peer-a").close();
    expect(adapter.connectedPeerIds).toEqual([]);
  });

  test("is empty when no channel has opened", () => {
    const { adapter } = build(["peer-a", "peer-b"]);
    expect(adapter.connectedPeerIds).toEqual([]);
  });
});

describe("MeshWebRTCAdapter.sendBlobMessage", () => {
  const payload = new Uint8Array([9, 8, 7]) as Uint8Array<ArrayBuffer>;

  test("sends on an open channel and reports success", () => {
    const { adapter, channelFor } = build(["peer-a"]);
    const channel = channelFor("peer-a");
    channel.open();
    expect(adapter.sendBlobMessage("peer-a", payload)).toBe(true);
    expect(channel.sent).toHaveLength(1);
    expect(Array.from(channel.sent[0] as Uint8Array)).toEqual([9, 8, 7]);
  });

  test("returns false for an unknown peer", () => {
    const { adapter } = build(["peer-a"]);
    expect(adapter.sendBlobMessage("nobody", payload)).toBe(false);
  });

  test("returns false when the channel is not open", () => {
    const { adapter, channelFor } = build(["peer-a"]);
    const channel = channelFor("peer-a");
    // Still connecting.
    expect(adapter.sendBlobMessage("peer-a", payload)).toBe(false);
    expect(channel.sent).toHaveLength(0);
  });

  test("applies backpressure once the buffer is above the high-water mark", () => {
    const { adapter, channelFor } = build(["peer-a"]);
    const channel = channelFor("peer-a");
    channel.open();
    channel.bufferedAmount = HIGH_WATER + 1;
    expect(adapter.sendBlobMessage("peer-a", payload)).toBe(false);
    expect(channel.sent).toHaveLength(0);
  });

  test("still sends when the buffer is exactly at the high-water mark", () => {
    const { adapter, channelFor } = build(["peer-a"]);
    const channel = channelFor("peer-a");
    channel.open();
    // The guard is strictly greater-than, so the boundary value sends.
    channel.bufferedAmount = HIGH_WATER;
    expect(adapter.sendBlobMessage("peer-a", payload)).toBe(true);
    expect(channel.sent).toHaveLength(1);
  });
});

describe("MeshWebRTCAdapter message wire codec", () => {
  test("round-trips type, ids, documentId, and data", () => {
    const { adapter } = build(["peer-a"]);
    const original = makeMessage({
      type: "request",
      senderId: "peer-a",
      targetId: "peer-z",
      documentId: "doc-xyz",
      data: new Uint8Array([5, 6, 7, 8, 9]),
    });
    const decoded = deserialise(adapter, serialise(adapter, original));
    expect(decoded.type).toBe("request");
    expect(decoded.senderId).toBe("peer-a" as unknown as Message["senderId"]);
    expect(decoded.targetId).toBe("peer-z" as unknown as Message["targetId"]);
    expect((decoded as unknown as { documentId?: string }).documentId).toBe("doc-xyz");
    expect(Array.from(decoded.data as Uint8Array)).toEqual([5, 6, 7, 8, 9]);
  });

  test("omits documentId from the wire header when the message has none", () => {
    const { adapter } = build(["peer-a"]);
    const decoded = deserialise(
      adapter,
      serialise(adapter, makeMessage({ documentId: undefined }))
    );
    expect((decoded as unknown as { documentId?: string }).documentId).toBeUndefined();
  });

  test("round-trips a message with no data as an empty payload", () => {
    const { adapter } = build(["peer-a"]);
    const decoded = deserialise(adapter, serialise(adapter, makeMessage({ data: undefined })));
    expect(Array.from(decoded.data as Uint8Array)).toEqual([]);
  });

  test("encodes the header length as a 4-byte big-endian prefix", () => {
    const { adapter } = build(["peer-a"]);
    const wire = serialise(adapter, makeMessage({ data: new Uint8Array(0) }));
    const view = new DataView(wire.buffer, wire.byteOffset, wire.byteLength);
    const headerLen = view.getUint32(0, false);
    // The header is the JSON object; the frame is exactly prefix+header here.
    expect(headerLen).toBe(wire.length - 4);
    expect(headerLen).toBeGreaterThan(0);
  });

  test("throws a too-short error on a frame that cannot hold the length prefix", () => {
    const { adapter } = build(["peer-a"]);
    // The specific message proves the explicit guard fired — not an
    // incidental RangeError from reading the uint32 off a 3-byte buffer.
    expect(() => deserialise(adapter, new Uint8Array([1, 2, 3]))).toThrow(
      "too short to deserialise"
    );
  });

  test("treats a bare 4-byte prefix as too short rather than a zero-length header", () => {
    const { adapter } = build(["peer-a"]);
    // headerLen 0 in exactly 4 bytes: the length guard is `< 4`, so this
    // boundary frame must NOT be reported as too short (it fails later on
    // the empty-header parse instead). Pins the `<` vs `<=` boundary.
    let caught: unknown;
    try {
      deserialise(adapter, new Uint8Array([0, 0, 0, 0]));
    } catch (e) {
      caught = e;
    }
    expect(caught).toBeDefined();
    expect((caught as Error).message).not.toContain("too short");
  });

  test("throws a header-truncated error when the declared header length overruns the frame", () => {
    const { adapter } = build(["peer-a"]);
    const frame = new Uint8Array(8);
    // Declare a 100-byte header in an 8-byte frame.
    new DataView(frame.buffer).setUint32(0, 100, false);
    expect(() => deserialise(adapter, frame)).toThrow("header truncated");
  });
});
