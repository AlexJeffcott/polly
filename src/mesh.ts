/**
 * @fairfox/polly/mesh — mesh-networked CRDT state with end-to-end encryption.
 *
 * Wraps the peer-first primitives with WebRTC mesh transport and
 * sign-then-encrypt envelopes. This subpath export isolates the
 * @automerge/* and tweetnacl dependency trees so consumers who only
 * use $sharedState / $syncedState / $resource never pull them in.
 *
 * @example
 * ```typescript
 * import { $meshState, configureMeshState } from "@fairfox/polly/mesh";
 * ```
 */

export type {
  EncryptedEnvelope,
  SealedBytes,
} from "./shared/lib/encryption";
export {
  decrypt,
  decryptOrThrow,
  EncryptionError,
  encrypt,
  generateDocumentKey,
  KEY_BYTES as ENCRYPTION_KEY_BYTES,
  NONCE_BYTES as ENCRYPTION_NONCE_BYTES,
  TAG_BYTES as ENCRYPTION_TAG_BYTES,
} from "./shared/lib/encryption";

// Mesh network adapter (sign-then-encrypt envelopes over any base adapter)
export type {
  MeshKeyring,
  MeshNetworkAdapterOptions,
} from "./shared/lib/mesh-network-adapter";
export {
  DEFAULT_MESH_KEY_ID,
  MeshNetworkAdapter,
} from "./shared/lib/mesh-network-adapter";
// Mesh signaling client
export type {
  MeshSignalingClientOptions,
  SignalingMessage as MeshSignalingMessage,
} from "./shared/lib/mesh-signaling-client";
export { MeshSignalingClient } from "./shared/lib/mesh-signaling-client";
// Mesh state wrappers
export type { MeshStateOptions } from "./shared/lib/mesh-state";
export {
  $meshCounter,
  $meshList,
  $meshState,
  $meshText,
  configureMeshState,
  resetMeshState,
} from "./shared/lib/mesh-state";
// Mesh WebRTC adapter
export type { MeshWebRTCAdapterOptions } from "./shared/lib/mesh-webrtc-adapter";
export { DEFAULT_ICE_SERVERS, MeshWebRTCAdapter } from "./shared/lib/mesh-webrtc-adapter";
// Pairing and revocation (depend on signing/encryption)
export type {
  CreatePairingTokenOptions,
  PairingToken,
} from "./shared/lib/pairing";
export {
  applyPairingToken,
  createPairingToken,
  createPairingTokenWithFreshIdentity,
  DEFAULT_PAIRING_TTL_MS,
  decodePairingToken,
  encodePairingToken,
  isPairingTokenExpired,
  PAIRING_NONCE_BYTES,
  PAIRING_TOKEN_VERSION,
  PairingError,
  parsePairingToken,
  serialisePairingToken,
} from "./shared/lib/pairing";
export type {
  CreateRevocationOptions,
  RevocationRecord,
} from "./shared/lib/revocation";
export {
  applyRevocation,
  createRevocation,
  decodeRevocation,
  encodeRevocation,
  REVOCATION_MAGIC,
  REVOCATION_RECORD_VERSION,
  RevocationError,
  revokePeerLocally,
} from "./shared/lib/revocation";
// Cryptographic primitives (signing + encryption)
export type { SignedEnvelope, SigningKeyPair } from "./shared/lib/signing";
export {
  generateSigningKeyPair,
  PUBLIC_KEY_BYTES as SIGNING_PUBLIC_KEY_BYTES,
  SECRET_KEY_BYTES as SIGNING_SECRET_KEY_BYTES,
  SIGNATURE_BYTES as SIGNING_SIGNATURE_BYTES,
  SigningError,
  sign,
  signingKeyPairFromSecret,
  verify,
} from "./shared/lib/signing";
