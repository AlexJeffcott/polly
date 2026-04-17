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
  /** The local node's keyring. The adapter signs every outgoing message
   * with `identity.secretKey` and verifies every incoming message against
   * the public keys in `knownPeers`. */
  keyring: MeshKeyring;
  /** When false, the adapter signs but does not encrypt. Outgoing messages
   * carry a signature envelope but the payload is plaintext; incoming
   * messages are verified against the sender's public key without a
   * decryption step. This mode is used by $peerState's `sign: true`
   * option, where the server must still be able to parse Automerge sync
   * messages. Defaults to true (encrypt + sign, the full $meshState
   * posture). */
  encryptionEnabled?: boolean;
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
  readonly keyring: MeshKeyring;
  readonly encryptionEnabled: boolean;

  constructor(options: MeshNetworkAdapterOptions) {
    super();
    this.base = options.base;
    this.keyring = options.keyring;
    this.encryptionEnabled = options.encryptionEnabled ?? true;

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
   */
  private wrap(message: Message): Message {
    const serialised = serialiseMessage(message);

    let payloadToSign: Uint8Array;
    if (this.encryptionEnabled) {
      const docKey = this.keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
      if (!docKey) {
        throw new Error(
          `MeshNetworkAdapter: missing document encryption key under id "${DEFAULT_MESH_KEY_ID}". Provision the key in the keyring before sending.`
        );
      }
      const encrypted = sealEncryptedEnvelope(serialised, DEFAULT_MESH_KEY_ID, docKey);
      payloadToSign = encodeEncryptedEnvelope(encrypted);
    } else {
      payloadToSign = serialised;
    }

    const signed = signEnvelope(payloadToSign, message.senderId, this.keyring.identity.secretKey);
    const signedBytes = encodeSignedEnvelope(signed);

    return {
      type: message.type,
      senderId: message.senderId,
      targetId: message.targetId,
      data: signedBytes,
    } as unknown as Message;
  }

  /**
   * Try to unwrap an incoming crypto-wrapped message. Returns the original
   * Message on success, undefined on verification or decryption failure.
   */
  private tryUnwrap(message: Message): Message | undefined {
    if (!message.data) return undefined;

    let signed: ReturnType<typeof decodeSignedEnvelope>;
    try {
      signed = decodeSignedEnvelope(message.data);
    } catch {
      return undefined;
    }

    // Drop messages from peers whose keys have been revoked, even if the
    // public key is still present in knownPeers. The revocation set is the
    // authoritative "this peer is no longer trusted" marker.
    if (this.keyring.revokedPeers.has(signed.senderId)) {
      return undefined;
    }

    const senderKey = this.keyring.knownPeers.get(signed.senderId);
    if (!senderKey) {
      return undefined;
    }

    let verifiedPayload: Uint8Array;
    try {
      verifiedPayload = openSignedEnvelope(signed, senderKey);
    } catch {
      return undefined;
    }

    if (!this.encryptionEnabled) {
      // Sign-only mode: the verified payload IS the serialised message.
      return deserialiseMessage(verifiedPayload);
    }

    // Full encrypt+sign mode: unwrap the encryption envelope.
    let encrypted: ReturnType<typeof decodeEncryptedEnvelope>;
    try {
      encrypted = decodeEncryptedEnvelope(verifiedPayload);
    } catch {
      return undefined;
    }

    const docKey = this.keyring.documentKeys.get(encrypted.documentId);
    if (!docKey) {
      return undefined;
    }

    let plaintext: Uint8Array;
    try {
      plaintext = openEncryptedEnvelope(encrypted, docKey);
    } catch {
      return undefined;
    }

    return deserialiseMessage(plaintext);
  }
}

// ─── message serialisation ─────────────────────────────────────────────────

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
