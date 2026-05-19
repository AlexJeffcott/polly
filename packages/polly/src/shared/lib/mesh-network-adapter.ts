/**
 * mesh-network-adapter — Phase 2 wrapping NetworkAdapter that adds Polly's
 * mesh-transport semantics on top of any underlying Automerge NetworkAdapter.
 *
 * The mesh transport's job is to make every message between peers signed
 * and encrypted before it reaches the wire. Rather than reimplementing the
 * Automerge sync protocol, this adapter takes a base adapter (in production
 * a real WebRTC or WebSocket adapter; in tests an in-memory loopback) and
 * applies the crypto envelope to every message that flows through.
 *
 * Outgoing path (Repo → wire):
 *   1. The Repo's NetworkSubsystem calls send(message) on this adapter.
 *   2. We serialise the message to bytes, encrypt them under the local
 *      keyring's document key, sign the resulting blob with the local
 *      identity's secret key, and pack the pair into a MeshFrame.
 *   3. We hand the MeshFrame off to the base adapter, which puts it on
 *      whatever wire it owns.
 *
 * Incoming path (wire → Repo):
 *   1. The base adapter emits a 'message' event with bytes from the wire.
 *   2. We unpack the MeshFrame, look up the sender's public key in the
 *      keyring, verify the signature, look up the document key, decrypt
 *      the payload, and deserialise it back to the original message.
 *   3. We re-emit the 'message' event upward to the Repo's NetworkSubsystem
 *      with the decrypted message.
 *
 * The keyring is an injected dependency. In production it's backed by
 * persistent storage and populated through the pairing flow. For tests it
 * is just a Map of publicly-known fixtures that both sides share.
 *
 * Caveat for the Phase 2 first cut: Automerge sync messages don't have a
 * stable "what document does this belong to" field at the wire level (the
 * documentId is part of the message contents). The mesh adapter therefore
 * uses a single per-Repo encryption key for now rather than per-document
 * keys, and stores the key once in the keyring under the well-known id
 * "polly-mesh-default". The plan describes per-document keys as the right
 * end state; that requires either parsing the message to extract the
 * documentId before encrypting (peeking inside the binary protocol) or
 * threading the document context through the network subsystem (which
 * needs upstream support). A follow-up will address this.
 */

import {
  type Message,
  NetworkAdapter,
  type PeerId,
  type PeerMetadata,
} from "@automerge/automerge-repo/slim";
import {
  decodeEncryptedEnvelope,
  encodeEncryptedEnvelope,
  openEnvelope as openEncryptedEnvelope,
  sealEnvelope as sealEncryptedEnvelope,
} from "./encryption";
import { emitMeshDiagnostic } from "./mesh-diagnostics";
import {
  decodeSignedEnvelope,
  encodeSignedEnvelope,
  openEnvelope as openSignedEnvelope,
  type SigningKeyPair,
  signEnvelope,
} from "./signing";

/** The well-known document id used for the Phase 2 first-cut single-key
 * encryption mode. See the file-level comment for the per-document key
 * follow-up. */
export const DEFAULT_MESH_KEY_ID = "polly-mesh-default";

/**
 * Control-message type tags. Every mesh message carries a single tag
 * byte at the front of its plaintext payload, after decryption and
 * signature verification. The tag discriminates the inner contents so
 * future control flows (RFC-043 revocation propagation, future RFCs)
 * can share the same encrypted-signed envelope without re-versioning.
 *
 * 0x00 is the default Automerge sync-message channel that polly has
 * carried since the first cut. 0x01 and 0x02 are reserved for the
 * revocation flow designed in RFC-043; the adapter recognises them at
 * receive time but does not yet act on the payload — that lands in
 * the second RFC-043 PR. Tags 0x03 and above are unassigned; a
 * receiver that sees one emits `drop:unknown-control-type` and the
 * message is dropped.
 *
 * Wire format break: polly 0.70 and earlier do not prepend the tag
 * and do not strip it on receive. Mixing 0.70 and 0.71-plus peers on
 * the same mesh produces garbage on both sides. The break is
 * acknowledged in RFC-043 and required for the protocol-level
 * revocation feature; the alternative (a separate WebRTC data
 * channel) doubles transport complexity.
 */
export const MESH_CONTROL_TYPE = {
  /** Automerge sync message — the default channel. */
  Sync: 0x00,
  /** A signed RevocationRecord (RFC-043). Receive-side dispatch is
   *  wired in this PR; the apply-and-persist behaviour lands in the
   *  next RFC-043 PR. */
  Revocation: 0x01,
  /** A revocation-set summary exchanged on every new peer connection
   *  to gossip revocations to peers that were offline at issue-time
   *  (RFC-043). Same staging as Revocation. */
  RevocationSummary: 0x02,
} as const;
export type MeshControlType = (typeof MESH_CONTROL_TYPE)[keyof typeof MESH_CONTROL_TYPE];

/**
 * A mesh keyring holds the local peer's signing identity, the public keys
 * of every peer the local node will accept messages from, the symmetric
 * encryption keys for documents the local node has access to, and the set
 * of peers whose keys have been revoked.
 */
export interface MeshKeyring {
  /** The local peer's signing keypair. The secret never leaves this
   * keyring; the public key is gossiped through the access set. */
  identity: SigningKeyPair;
  /** Map from peer id (string) to that peer's signing public key. The
   * mesh adapter rejects messages from peers not present in this map. */
  knownPeers: Map<string, Uint8Array>;
  /** Map from document key id (typically the documentId, or the well-known
   * default for the single-key first cut) to the symmetric encryption key. */
  documentKeys: Map<string, Uint8Array>;
  /** Set of peer ids whose keys have been revoked. The mesh adapter drops
   * incoming messages from any peer in this set, even if the peer is still
   * present in {@link knownPeers}. Revocation is applied via the revocation
   * module; the set is kept separate from knownPeers so that an application
   * can audit who was once authorised without losing the revocation record. */
  revokedPeers: Set<string>;
  /** Optional set of peer ids authorised to issue revocations. When present
   * and non-empty, `decodeRevocation` accepts a signed record only if the
   * issuer is in this set. When undefined or empty, any signed revocation
   * from a known peer is accepted (the Phase 2 first-cut default). This
   * field layers a "who can revoke whom" check on top of the signature
   * layer without breaking existing callers. */
  revocationAuthority?: Set<string>;
}

/**
 * Constructor options for {@link MeshNetworkAdapter}.
 */
export interface MeshNetworkAdapterOptions {
  /** The underlying NetworkAdapter that puts crypto-wrapped bytes on the
   * wire. In production this is a WebRTC or WebSocket adapter; in tests
   * it's an in-memory loopback. */
  base: NetworkAdapter;
  /** A synchronous function that returns the keyring to use for the next
   * send or receive. The adapter never caches the value across calls —
   * every {@link MeshNetworkAdapter#send | send} and every incoming
   * message asks the source for the current keyring, so callers that
   * mutate the in-memory keyring (e.g. `applyPairingToken`) or re-issue
   * it entirely (e.g. a long-lived CLI watching a disk-backed keyring
   * file that another process can rewrite) see their updates take effect
   * on the very next message without restarting the adapter.
   *
   * The function must be synchronous because Automerge's
   * `NetworkAdapter.send` is synchronous. Implementations that need to
   * read from disk should maintain a cached object — refreshed by a
   * file watcher, a manual reload, or `readFileSync` per call — and
   * return that cached object from the source. */
  keyringSource: () => MeshKeyring;
  /** When false, the adapter signs but does not encrypt. Outgoing messages
   * carry a signature envelope but the payload is plaintext; incoming
   * messages are verified against the sender's public key without a
   * decryption step. This mode is used by $peerState's `sign: true`
   * option, where the server must still be able to parse Automerge sync
   * messages. Defaults to true (encrypt + sign, the full $meshState
   * posture). */
  encryptionEnabled?: boolean;
  /**
   * Optional handler for non-Sync control messages (RFC-043). Called
   * after signature verification and decryption with the type tag,
   * the body bytes that followed the tag, and the verified senderId.
   * The handler owns the apply-and-persist behaviour for whichever
   * control flow the tag belongs to; the adapter routes only.
   *
   * The handler is called *after* the corresponding `ctrl:*-received`
   * diagnostic fires, so subscribers observing the low-level signal
   * see the event before the handler mutates any application state.
   * Handler exceptions are swallowed by the adapter — a buggy handler
   * cannot tear the network path — but a diagnostic
   * `drop:control-handler-threw` is emitted so the failure is
   * observable.
   */
  onControlMessage?: (tag: number, body: Uint8Array, senderId: string) => void;
}

/**
 * NetworkAdapter that wraps another adapter with Polly's mesh-transport
 * crypto envelope. Every outgoing message is encrypted then signed; every
 * incoming message is verified then decrypted before being forwarded to
 * the Repo's network subsystem.
 *
 * The adapter delegates lifecycle (connect, disconnect, isReady, peer
 * discovery) to the base adapter unchanged. Only the message body is
 * intercepted.
 */
export class MeshNetworkAdapter extends NetworkAdapter {
  readonly base: NetworkAdapter;
  readonly keyringSource: () => MeshKeyring;
  readonly encryptionEnabled: boolean;
  readonly onControlMessage:
    | ((tag: number, body: Uint8Array, senderId: string) => void)
    | undefined;

  /** Read-only view of the current keyring. Each access calls
   * {@link MeshNetworkAdapterOptions.keyringSource}, so the value
   * reflects whatever mutations or swaps the caller has applied since
   * the last access — the same contract the send and receive paths
   * follow internally. */
  get keyring(): MeshKeyring {
    return this.keyringSource();
  }

  constructor(options: MeshNetworkAdapterOptions) {
    super();
    this.base = options.base;
    this.keyringSource = options.keyringSource;
    this.encryptionEnabled = options.encryptionEnabled ?? true;
    this.onControlMessage = options.onControlMessage;

    // Forward lifecycle and peer events from the base adapter.
    this.base.on("close", () => this.emit("close"));
    this.base.on("peer-candidate", (payload) => this.emit("peer-candidate", payload));
    this.base.on("peer-disconnected", (payload) => this.emit("peer-disconnected", payload));

    // Intercept incoming messages: the base adapter will surface them as
    // 'message' events with crypto-wrapped payloads. We unwrap and re-emit.
    this.base.on("message", (rawMessage) => {
      const unwrapped = this.tryUnwrap(rawMessage);
      if (unwrapped) {
        this.emit("message", unwrapped);
      }
      // Silently drop messages that fail verification or decryption. A
      // production adapter would surface this through a diagnostic channel
      // so the application could prompt the user; the Phase 2 first cut
      // logs through the standard "drop unknown" semantics of the network
      // subsystem.
    });
  }

  isReady(): boolean {
    return this.base.isReady();
  }

  whenReady(): Promise<void> {
    return this.base.whenReady();
  }

  connect(peerId: PeerId, peerMetadata?: PeerMetadata): void {
    this.peerId = peerId;
    if (peerMetadata !== undefined) {
      this.peerMetadata = peerMetadata;
    }
    this.base.connect(peerId, peerMetadata);
  }

  disconnect(): void {
    this.base.disconnect();
  }

  send(message: Message): void {
    const wrapped = this.wrap(message);
    this.base.send(wrapped);
  }

  /**
   * Wrap an outgoing Automerge message in an encrypt-then-sign envelope.
   * The wrapped payload is returned as a Message with the original sender
   * and target ids and the crypto blob in the `data` field.
   *
   * The serialised Automerge message is prefixed with a one-byte
   * control-type tag (RFC-043). For outgoing Automerge sync this is
   * always {@link MESH_CONTROL_TYPE.Sync} (0x00); the tag exists so
   * future control flows (revocation propagation, revocation-set
   * summaries) can share the same encrypted-signed envelope without
   * re-versioning the wire format.
   */
  private wrap(message: Message): Message {
    const keyring = this.keyringSource();
    const serialised = serialiseMessage(message);
    const tagged = prependControlTag(MESH_CONTROL_TYPE.Sync, serialised);

    let payloadToSign: Uint8Array;
    if (this.encryptionEnabled) {
      const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
      if (!docKey) {
        throw new Error(
          `MeshNetworkAdapter: missing document encryption key under id "${DEFAULT_MESH_KEY_ID}". Provision the key in the keyring before sending.`
        );
      }
      const encrypted = sealEncryptedEnvelope(tagged, DEFAULT_MESH_KEY_ID, docKey);
      payloadToSign = encodeEncryptedEnvelope(encrypted);
    } else {
      payloadToSign = tagged;
    }

    const signed = signEnvelope(payloadToSign, message.senderId, keyring.identity.secretKey);
    const signedBytes = encodeSignedEnvelope(signed);

    // Preserve `documentId` on the outer envelope so the base adapter
    // (MeshWebRTCAdapter) can stamp per-handle wire-level bookkeeping
    // without parsing the encrypted payload. The inner serialised
    // message also carries documentId, which the receiver uses after
    // crypto-unwrap; this outer copy is purely for the sender-side
    // observability path that polly#107 item 7 specifies. The signed
    // envelope still binds the inner copy, so the outer copy cannot
    // forge routing — a peer that mismatches the two is observable as
    // a divergent receive shape, not a routing exploit.
    const outer: Record<string, unknown> = {
      type: message.type,
      senderId: message.senderId,
      targetId: message.targetId,
      data: signedBytes,
    };
    if ("documentId" in message && (message as { documentId?: unknown }).documentId !== undefined) {
      outer["documentId"] = (message as { documentId: unknown }).documentId;
    }
    return outer as unknown as Message;
  }

  // Try to unwrap an incoming crypto-wrapped message. Returns the original
  // Message on success, undefined on verification or decryption failure.
  // Each silent-drop branch emits one typed diagnostic via
  // mesh-diagnostics; the per-branch mapping is the contract that module
  // advertises, which is why the function reads as seven sequential
  // checks rather than a collapsed helper.
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: seven silent-drop branches each emit one typed diagnostic — the per-branch contract is the source of truth the mesh-diagnostics stream advertises.
  private tryUnwrap(message: Message): Message | undefined {
    if (!message.data) return undefined;

    let signed: ReturnType<typeof decodeSignedEnvelope>;
    try {
      signed = decodeSignedEnvelope(message.data);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "drop:malformed-signed-envelope",
        reason: err instanceof Error ? err.message : String(err),
      });
      return undefined;
    }

    // Re-read the keyring on every incoming message. This is what makes a
    // post-construction peer addition take effect — if the caller has
    // mutated the keyring's `knownPeers` map (or swapped the keyring
    // object outright via a file watcher), the new entry is visible here
    // without any restart or explicit notification path. See issue #100.
    const keyring = this.keyringSource();

    // Drop messages from peers whose keys have been revoked, even if the
    // public key is still present in knownPeers. The revocation set is the
    // authoritative "this peer is no longer trusted" marker.
    if (keyring.revokedPeers.has(signed.senderId)) {
      emitMeshDiagnostic({
        kind: "drop:revoked-peer",
        senderId: signed.senderId,
      });
      return undefined;
    }

    const senderKey = keyring.knownPeers.get(signed.senderId);
    if (!senderKey) {
      emitMeshDiagnostic({
        kind: "drop:unknown-peer",
        senderId: signed.senderId,
      });
      return undefined;
    }

    let verifiedPayload: Uint8Array;
    try {
      verifiedPayload = openSignedEnvelope(signed, senderKey);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "drop:bad-signature",
        senderId: signed.senderId,
        reason: err instanceof Error ? err.message : String(err),
      });
      return undefined;
    }

    if (!this.encryptionEnabled) {
      // Sign-only mode: the verified payload IS the tagged plaintext.
      return this.dispatchTaggedPayload(verifiedPayload, signed.senderId);
    }

    // Full encrypt+sign mode: unwrap the encryption envelope.
    let encrypted: ReturnType<typeof decodeEncryptedEnvelope>;
    try {
      encrypted = decodeEncryptedEnvelope(verifiedPayload);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "drop:malformed-encrypted-envelope",
        senderId: signed.senderId,
        reason: err instanceof Error ? err.message : String(err),
      });
      return undefined;
    }

    const docKey = keyring.documentKeys.get(encrypted.documentId);
    if (!docKey) {
      emitMeshDiagnostic({
        kind: "drop:missing-doc-key",
        senderId: signed.senderId,
        documentId: encrypted.documentId,
      });
      return undefined;
    }

    let plaintext: Uint8Array;
    try {
      plaintext = openEncryptedEnvelope(encrypted, docKey);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "drop:bad-decryption",
        senderId: signed.senderId,
        documentId: encrypted.documentId,
        reason: err instanceof Error ? err.message : String(err),
      });
      return undefined;
    }

    return this.dispatchTaggedPayload(plaintext, signed.senderId);
  }

  /**
   * Dispatch a verified-and-decrypted plaintext payload based on its
   * one-byte control-type tag (RFC-043). For {@link MESH_CONTROL_TYPE.Sync}
   * the remainder is the serialised Automerge message and is returned
   * to the caller. For revocation tags the dispatch emits a
   * `ctrl:*-received` diagnostic and drops the payload at this layer
   * pending the next RFC-043 PR. Unknown tags emit
   * `drop:unknown-control-type` and drop.
   */
  private dispatchTaggedPayload(payload: Uint8Array, senderId: string): Message | undefined {
    if (payload.byteLength < 1) {
      emitMeshDiagnostic({ kind: "drop:empty-control-payload", senderId });
      return undefined;
    }
    const tag = payload[0] as number;
    const body = payload.subarray(1);
    switch (tag) {
      case MESH_CONTROL_TYPE.Sync:
        return deserialiseMessage(body);
      case MESH_CONTROL_TYPE.Revocation:
        emitMeshDiagnostic({ kind: "ctrl:revocation-received", senderId });
        this.invokeControlHandler(tag, body, senderId);
        return undefined;
      case MESH_CONTROL_TYPE.RevocationSummary:
        emitMeshDiagnostic({
          kind: "ctrl:revocation-summary-received",
          senderId,
        });
        this.invokeControlHandler(tag, body, senderId);
        return undefined;
      default:
        emitMeshDiagnostic({
          kind: "drop:unknown-control-type",
          senderId,
          tag,
        });
        return undefined;
    }
  }

  private invokeControlHandler(tag: number, body: Uint8Array, senderId: string): void {
    if (!this.onControlMessage) return;
    try {
      this.onControlMessage(tag, body, senderId);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "drop:control-handler-threw",
        senderId,
        tag,
        reason: err instanceof Error ? err.message : String(err),
      });
    }
  }

  /**
   * Send a control message (RFC-043) to a list of connected peers.
   * The body is wrapped in the same encrypt-sign envelope Automerge
   * sync uses; the type tag goes in front so receivers route it to
   * {@link MeshNetworkAdapterOptions.onControlMessage}.
   *
   * The base adapter does not surface its connected-peer set on the
   * NetworkAdapter interface, so the caller passes the targets
   * explicitly. The MeshClient layer maintains that list from the
   * `peer-candidate` / `peer-disconnected` events.
   */
  sendControlMessage(
    tag: MeshControlType,
    body: Uint8Array,
    targetPeerIds: ReadonlyArray<PeerId>
  ): void {
    if (targetPeerIds.length === 0) return;
    const keyring = this.keyringSource();
    const tagged = prependControlTag(tag, body);

    let payloadToSign: Uint8Array;
    if (this.encryptionEnabled) {
      const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
      if (!docKey) {
        throw new Error(
          `MeshNetworkAdapter.sendControlMessage: missing document encryption key under id "${DEFAULT_MESH_KEY_ID}".`
        );
      }
      const encrypted = sealEncryptedEnvelope(tagged, DEFAULT_MESH_KEY_ID, docKey);
      payloadToSign = encodeEncryptedEnvelope(encrypted);
    } else {
      payloadToSign = tagged;
    }

    const senderId = (this.peerId ?? "") as PeerId;
    const signed = signEnvelope(payloadToSign, senderId, keyring.identity.secretKey);
    const signedBytes = encodeSignedEnvelope(signed);

    for (const targetId of targetPeerIds) {
      const outer: Record<string, unknown> = {
        type: "sync",
        senderId,
        targetId,
        data: signedBytes,
      };
      this.base.send(outer as unknown as Message);
    }
  }
}

/**
 * Prepend a one-byte control-type tag to a payload. The tag goes
 * inside the encrypted-signed envelope (or directly inside the signed
 * envelope in sign-only mode), so it is both confidential (encrypted
 * when encryption is enabled) and authenticated (covered by the
 * signature). Exposed so future RFC-043 issue helpers can build
 * tagged payloads without rebuilding this primitive.
 */
export function prependControlTag(tag: MeshControlType, body: Uint8Array): Uint8Array {
  const out = new Uint8Array(body.byteLength + 1);
  out[0] = tag;
  out.set(body, 1);
  return out;
}

// message serialisation

/**
 * Serialise an Automerge sync message to a binary blob suitable for
 * encryption. The format is a length-prefixed JSON header (carrying the
 * non-binary fields) followed by the raw `data` bytes (which Automerge's
 * sync messages carry as Uint8Array). This avoids round-tripping the
 * binary payload through JSON, which would balloon its size.
 */
function serialiseMessage(message: Message): Uint8Array {
  const headerObj: Record<string, unknown> = {
    type: message.type,
    senderId: message.senderId,
    targetId: message.targetId,
  };
  if ("documentId" in message && message.documentId !== undefined) {
    headerObj["documentId"] = message.documentId;
  }
  if ("count" in message && message.count !== undefined) {
    headerObj["count"] = message.count;
  }
  if ("sessionId" in message && message.sessionId !== undefined) {
    headerObj["sessionId"] = message.sessionId;
  }
  const headerBytes = new TextEncoder().encode(JSON.stringify(headerObj));
  const dataBytes: Uint8Array =
    "data" in message && message.data instanceof Uint8Array ? message.data : new Uint8Array(0);

  const out = new Uint8Array(4 + headerBytes.length + dataBytes.length);
  const view = new DataView(out.buffer);
  view.setUint32(0, headerBytes.length, false);
  out.set(headerBytes, 4);
  out.set(dataBytes, 4 + headerBytes.length);
  return out;
}

/**
 * Inverse of {@link serialiseMessage}.
 */
function deserialiseMessage(bytes: Uint8Array): Message {
  if (bytes.length < 4) {
    throw new Error("MeshNetworkAdapter: message too short to deserialise.");
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const headerLen = view.getUint32(0, false);
  if (bytes.length < 4 + headerLen) {
    throw new Error("MeshNetworkAdapter: message header truncated.");
  }
  const header = JSON.parse(new TextDecoder().decode(bytes.subarray(4, 4 + headerLen)));
  const data = bytes.slice(4 + headerLen);
  return { ...header, data } as unknown as Message;
}
