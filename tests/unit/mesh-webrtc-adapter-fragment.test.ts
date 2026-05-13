/**
 * Adapter-level tests for the SCTP-cap fragmentation path.
 *
 * Proves the property the live #101 repro exercises: an outgoing Automerge
 * sync message above the data-channel maxMessageSize is split into ordered
 * fragments before any RTCDataChannel.send call, and the receive path
 * reassembles those fragments back into the original Message event.
 *
 * The adapter is wired against a hand-rolled FakePeerConnection / FakeDataChannel
 * pair (no real WebRTC) so the test can sit on top of bun:test.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import type { Message } from "@automerge/automerge-repo/slim";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";
import {
  isSyncFragmentType,
  parseSyncFragment,
  SYNC_FRAGMENT_THRESHOLD,
} from "@/shared/lib/sync-fragment";

class FakeDataChannel {
  onopen: (() => void) | null = null;
  onmessage: ((ev: { data: ArrayBuffer | Uint8Array }) => void) | null = null;
  onclose: (() => void) | null = null;
  readyState: "connecting" | "open" | "closed" = "connecting";
  sent: Uint8Array[] = [];

  open(): void {
    this.readyState = "open";
    this.onopen?.();
  }

  send(bytes: Uint8Array<ArrayBuffer>): void {
    // Defensive: a real RTCDataChannel rejects sends above maxMessageSize.
    // Fail the test loudly so a regression is impossible to miss.
    if (bytes.length > 256 * 1024) {
      throw new Error(
        `FakeDataChannel: send(${bytes.length}) above 256 KiB cap — fragmentation regression`
      );
    }
    this.sent.push(new Uint8Array(bytes));
  }

  deliver(bytes: Uint8Array): void {
    // The adapter's channel.onmessage handler accepts either ArrayBuffer
    // or Uint8Array; the live WebRTC path delivers ArrayBuffer, so pass a
    // fresh ArrayBuffer copy here to mirror that surface.
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
    sendSignal(_target: string, _payload: unknown): boolean {
      return true;
    },
    connect: async (): Promise<void> => {},
    close: (): void => {},
  } as unknown as MeshSignalingClient;
}

function buildAdapterWithOpenChannel(): {
  adapter: MeshWebRTCAdapter;
  channel: FakeDataChannel;
  remotePeerId: string;
} {
  const localPeerId = "peer-z";
  const remotePeerId = "peer-a";
  const peerConnections: FakePeerConnection[] = [];
  class CapturingPC extends FakePeerConnection {
    constructor() {
      super();
      peerConnections.push(this);
    }
  }
  const adapter = new MeshWebRTCAdapter({
    signaling: createSignalingStub(localPeerId),
    peerId: localPeerId,
    knownPeerIds: [remotePeerId],
    RTCPeerConnection: CapturingPC as unknown as typeof RTCPeerConnection,
  });
  adapter.handlePeerJoined(remotePeerId);
  const channel = peerConnections[0]?.channel;
  if (!channel) throw new Error("test setup: no data channel created");
  channel.open();
  return { adapter, channel, remotePeerId };
}

describe("MeshWebRTCAdapter SCTP-cap fragmentation", () => {
  let adapter: MeshWebRTCAdapter;
  let channel: FakeDataChannel;
  let remotePeerId: string;

  beforeEach(() => {
    ({ adapter, channel, remotePeerId } = buildAdapterWithOpenChannel());
  });

  test("sends a small message in a single non-fragment frame", () => {
    const message: Message = {
      type: "sync",
      senderId: "peer-z" as unknown as Message["senderId"],
      targetId: remotePeerId as unknown as Message["targetId"],
      documentId: "doc-small" as unknown as Message["documentId"],
      data: new Uint8Array([1, 2, 3, 4]),
    } as unknown as Message;
    adapter.send(message);
    expect(channel.sent).toHaveLength(1);
    const onlyFrame = channel.sent[0];
    if (!onlyFrame) throw new Error("expected one sent frame");
    expect(isSyncFragmentType(onlyFrame)).toBe(false);
  });

  test("fragments an oversized sync message into multiple sub-cap frames", () => {
    const payload = new Uint8Array(SYNC_FRAGMENT_THRESHOLD * 3 + 11);
    for (let i = 0; i < payload.length; i++) payload[i] = i & 0xff;
    const message: Message = {
      type: "sync",
      senderId: "peer-z" as unknown as Message["senderId"],
      targetId: remotePeerId as unknown as Message["targetId"],
      documentId: "doc-big" as unknown as Message["documentId"],
      data: payload,
    } as unknown as Message;
    adapter.send(message);
    expect(channel.sent.length).toBeGreaterThan(1);
    let fragmentId: string | undefined;
    let totalSeen = 0;
    const indices = new Set<number>();
    for (const frame of channel.sent) {
      expect(isSyncFragmentType(frame)).toBe(true);
      const parsed = parseSyncFragment(frame);
      if (!parsed) throw new Error("fragment did not parse");
      if (fragmentId === undefined) fragmentId = parsed.header.id;
      expect(parsed.header.id).toBe(fragmentId);
      expect(parsed.header.total).toBeGreaterThan(1);
      totalSeen = parsed.header.total;
      indices.add(parsed.header.index);
    }
    expect(indices.size).toBe(totalSeen);
    expect(channel.sent.length).toBe(totalSeen);
  });

  test("reassembles incoming fragments and emits the original message", async () => {
    const received: Message[] = [];
    adapter.on("message", (msg) => {
      received.push(msg);
    });

    // Build a synthetic oversized message on the wire as if peer-a had
    // just sent it: send through our own adapter to produce the wire
    // frames, then deliver them back through the channel's onmessage.
    // The senderId/targetId fields in the header are echoed by the
    // adapter's deserialiser, so we can verify the bytes survive intact.
    const original = new Uint8Array(SYNC_FRAGMENT_THRESHOLD * 2 + 5);
    for (let i = 0; i < original.length; i++) original[i] = (i * 7 + 1) & 0xff;
    const outgoing: Message = {
      type: "sync",
      senderId: "peer-z" as unknown as Message["senderId"],
      targetId: remotePeerId as unknown as Message["targetId"],
      documentId: "doc-roundtrip" as unknown as Message["documentId"],
      data: original,
    } as unknown as Message;
    adapter.send(outgoing);
    const wireFrames = [...channel.sent];
    channel.sent = [];

    for (const frame of wireFrames) {
      channel.deliver(frame);
    }
    // Reassembly schedules dispatch onto a fresh macrotask when
    // syncYieldEnabled is on (the default since polly #104), so wait
    // for the two timer rounds the fragment path uses — one to
    // dispatch the reassembled bytes, one to emit the deserialised
    // message — before asserting receipt.
    await new Promise((r) => setTimeout(r, 0));
    await new Promise((r) => setTimeout(r, 0));
    expect(received).toHaveLength(1);
    const reassembled = received[0];
    if (!reassembled) throw new Error("expected emitted message");
    expect(reassembled.type).toBe("sync");
    expect((reassembled as unknown as { documentId: string }).documentId).toBe("doc-roundtrip");
    const data = (reassembled as unknown as { data: Uint8Array }).data;
    expect(data.length).toBe(original.length);
    expect(data).toEqual(original);
  });

  test("out-of-order fragment delivery still reassembles correctly", async () => {
    const received: Message[] = [];
    adapter.on("message", (msg) => {
      received.push(msg);
    });
    const payload = new Uint8Array(SYNC_FRAGMENT_THRESHOLD * 2 + 1);
    for (let i = 0; i < payload.length; i++) payload[i] = (i + 13) & 0xff;
    const outgoing: Message = {
      type: "sync",
      senderId: "peer-z" as unknown as Message["senderId"],
      targetId: remotePeerId as unknown as Message["targetId"],
      documentId: "doc-reorder" as unknown as Message["documentId"],
      data: payload,
    } as unknown as Message;
    adapter.send(outgoing);
    const wireFrames = [...channel.sent].reverse();
    channel.sent = [];
    for (const frame of wireFrames) {
      channel.deliver(frame);
    }
    // Async dispatch — see neighbouring test for the rationale.
    await new Promise((r) => setTimeout(r, 0));
    await new Promise((r) => setTimeout(r, 0));
    expect(received).toHaveLength(1);
    const data = (received[0] as unknown as { data: Uint8Array }).data;
    expect(data).toEqual(payload);
  });
});
