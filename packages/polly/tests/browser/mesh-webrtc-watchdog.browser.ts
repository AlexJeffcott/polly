/**
 * Browser test for the polly#110 slot-liveness watchdog, end-to-end.
 *
 * polly#110: when a remote peer's process is killed without an
 * OS-layer FIN (SIGKILL, crash, network partition + restart), the
 * RTCPeerConnection stays at `connectionState === "connected"` for
 * many minutes while ICE keepalives slowly time out. The data
 * channel stays `open`. Outbound sync messages fire into the void
 * and nothing tears the slot down, so the recovery sweep hits
 * `slot-already-exists` forever.
 *
 * The fix is an application-layer watchdog: a slot that is
 * `connected` + data channel `open` but has had no inbound bytes
 * for `slotIdleTimeoutMs` is torn down so the recovery sweep can
 * re-attempt.
 *
 * The unit suite (tests/unit/mesh-webrtc-adapter-watchdog.test.ts)
 * proves the watchdog logic against a fake RTCPeerConnection. This
 * test proves it against a REAL Chrome WebRTC stack: two peers form
 * a genuine data-channel connection, one peer is then silenced at
 * the wire (its data channel `send` is neutered, simulating a killed
 * process whose connection has not yet FIN'd), and the surviving
 * peer's watchdog is observed tearing the now-dead slot down while
 * `connectionState` is still `connected`.
 */

import { type PeerId, Repo } from "@automerge/automerge-repo";
import { generateDocumentKey } from "../../src/shared/lib/encryption";
import {
  DEFAULT_MESH_KEY_ID,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "../../src/shared/lib/mesh-network-adapter";
import { MeshSignalingClient } from "../../src/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "../../src/shared/lib/mesh-webrtc-adapter";
import { generateSigningKeyPair } from "../../src/shared/lib/signing";
import { describe, done, expect, test, waitFor } from "../../tools/test/src/browser/harness";

// The signalling URL is injected by the runner via Bun.build define.
const SIGNALING_URL = process.env.SIGNALING_URL ?? "ws://127.0.0.1:39000/polly/signaling";

// A short idle timeout keeps the test inside the runner's per-file
// budget. The watchdog logic is timeout-agnostic; 2s is well past
// any healthy inbound cadence and far below the 120s production
// default.
const IDLE_TIMEOUT_MS = 2000;
const WATCHDOG_INTERVAL_MS = 300;

type Doc = { count: number };

/**
 * Neuter every data channel on an adapter's live slots: replace
 * `send` with a no-op so the peer emits no further application
 * bytes. The RTCPeerConnection stays alive, so the remote end keeps
 * seeing `connectionState === "connected"` — exactly the killed-
 * process-without-FIN shape polly#110 describes.
 */
function silenceAdapterWire(adapter: MeshWebRTCAdapter): number {
  const slots = (
    adapter as unknown as {
      slots: Map<string, { channel?: { send?: unknown } }>;
    }
  ).slots;
  let silenced = 0;
  for (const slot of slots.values()) {
    if (slot.channel) {
      Object.defineProperty(slot.channel, "send", {
        value: () => {},
        writable: true,
        configurable: true,
      });
      silenced += 1;
    }
  }
  return silenced;
}

describe("MeshWebRTCAdapter polly#110 watchdog in a real browser", () => {
  test("tears down a connected-but-silent slot once inbound bytes stop", async () => {
    console.log("[test] setting up keys");
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([["peer-b", bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([["peer-a", aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };

    console.log("[test] creating WebRTC adapters");

    // Peer A — the survivor. Its watchdog is the unit under test:
    // a short idle timeout, the never-connected gate disabled so
    // only the polly#110 idle path can fire.
    const webrtcA = new MeshWebRTCAdapter({
      signaling: null as unknown as MeshSignalingClient,
      peerId: "peer-a",
      knownPeerIds: ["peer-b"],
      slotIdleTimeoutMs: IDLE_TIMEOUT_MS,
      slotWatchdogIntervalMs: WATCHDOG_INTERVAL_MS,
      slotNeverConnectedTimeoutMs: 0,
    });

    const signalingA = new MeshSignalingClient({
      url: SIGNALING_URL,
      peerId: "peer-a",
      onSignal: (from, payload) => webrtcA.handleSignal(from, payload),
      onPeersPresent: (ids) => webrtcA.handlePeersPresent(ids),
      onPeerJoined: (id) => webrtcA.handlePeerJoined(id),
      onPeerLeft: (id) => webrtcA.handlePeerLeft(id),
    });
    Object.assign(webrtcA, { signaling: signalingA });

    // Peer B — the soon-to-be-killed peer. Its own watchdog is
    // disabled so the test isolates A's behaviour; B keeps receiving
    // A's traffic, it simply stops sending.
    const webrtcB = new MeshWebRTCAdapter({
      signaling: null as unknown as MeshSignalingClient,
      peerId: "peer-b",
      knownPeerIds: ["peer-a"],
      slotWatchdogIntervalMs: 0,
    });

    const signalingB = new MeshSignalingClient({
      url: SIGNALING_URL,
      peerId: "peer-b",
      onSignal: (from, payload) => webrtcB.handleSignal(from, payload),
      onPeersPresent: (ids) => webrtcB.handlePeersPresent(ids),
      onPeerJoined: (id) => webrtcB.handlePeerJoined(id),
      onPeerLeft: (id) => webrtcB.handlePeerLeft(id),
    });
    Object.assign(webrtcB, { signaling: signalingB });

    await signalingA.connect();
    await signalingB.connect();
    console.log("[test] signalling connected");

    const meshA = new MeshNetworkAdapter({ base: webrtcA, keyringSource: () => aKeyring });
    const meshB = new MeshNetworkAdapter({ base: webrtcB, keyringSource: () => bKeyring });

    const repoA = new Repo({ network: [meshA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [meshB], peerId: "peer-b" as unknown as PeerId });

    // Observe A's teardown signal.
    const disconnects: string[] = [];
    webrtcA.on("peer-disconnected", (payload: { peerId: PeerId }) => {
      disconnects.push(payload.peerId as unknown as string);
    });

    console.log("[test] waiting for peer connection");
    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0, 10000);
    console.log(`[test] peers connected: A=${repoA.peers.length} B=${repoB.peers.length}`);

    // Drive real bidirectional traffic so A's slot has a fresh
    // lastInboundAt: create on A, observe on B, mutate on B, observe
    // back on A. The mutation arriving on A is genuine inbound bytes.
    const handleA = repoA.create<Doc>({ count: 1 });
    await handleA.whenReady();
    const handleB = await repoB.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().count === 1;
      } catch {
        return false;
      }
    }, 8000);
    handleB.change((d) => {
      d.count = 2;
    });
    await waitFor(() => {
      try {
        return handleA.doc().count === 2;
      } catch {
        return false;
      }
    }, 8000);
    console.log("[test] bidirectional sync confirmed — slot is healthy");

    // The slot is connected and the data channel is open right now.
    const slotsA = (
      webrtcA as unknown as {
        slots: Map<string, { connection: RTCPeerConnection }>;
      }
    ).slots;
    const connBefore = slotsA.get("peer-b")?.connection.connectionState;
    console.log(`[test] A's slot connectionState before kill: ${connBefore}`);
    expect(connBefore).toBe("connected");
    expect(webrtcA.peerSlotCount()).toBe(1);

    // Kill peer B: silence its wire. The RTCPeerConnection stays
    // alive, so A's connectionState will NOT transition to
    // disconnected/failed — only the watchdog can save A now.
    const silenced = silenceAdapterWire(webrtcB);
    console.log(`[test] silenced ${silenced} of B's data channel(s) — B is now mute`);
    expect(silenced).toBeGreaterThan(0);

    // The watchdog should tear A's slot down once IDLE_TIMEOUT_MS of
    // silence elapses. Allow generous margin for the watchdog tick.
    console.log("[test] waiting for A's watchdog to tear down the dead slot");
    await waitFor(() => webrtcA.peerSlotCount() === 0, 8000);
    console.log("[test] A's slot torn down");

    // The teardown was the watchdog's idle path, not an OS-level
    // disconnect: connectionState was still "connected" and the
    // recorded reason names the idle gate.
    expect(webrtcA.peerSlotCount()).toBe(0);
    expect(disconnects).toContain("peer-b");

    const snap = webrtcA.getPeerStateSnapshot();
    const entry = snap.peers.find((p) => p.peerId === "peer-b");
    expect(entry?.slotInitiationDecision.reason).toBe("fatal-error");
    expect(entry?.slotInitiationDecision.error).toContain("idle");
    console.log(`[test] teardown reason: ${entry?.slotInitiationDecision.error}`);

    await repoA.shutdown();
    await repoB.shutdown();
    signalingA.close();
    signalingB.close();
    console.log("[test] done");
  });
});

done();
