/**
 * @fairfox/web-ext
 *
 * Main entry point for framework exports.
 * Users can import from '@fairfox/web-ext' to get common utilities.
 */

export type { ExtensionAdapters } from "./shared/adapters";
// Adapters
export { createChromeAdapters } from "./shared/adapters";
// Peer-first state primitives (RFC-041 Phase 0 — Automerge-backed CRDT primitives).
// Phase 1 will wrap these as $peerState / $peerText / $peerCounter / $peerList with
// the relay transport baked in; Phase 2 will wrap them again as $meshState / $mesh*
// with the WebRTC mesh transport. The base $crdt* family exposed here is
// transport-agnostic and accepts a caller-supplied async handle factory.
export type { Access, AccessPredicate, PeerIdentity } from "./shared/lib/access";
export {
  and,
  anyOfPeers,
  anyone,
  groupAccess,
  nobody,
  not,
  onlyPeer,
  or,
  ownerAccess,
  publicAccess,
  readOnlyExcept,
} from "./shared/lib/access";
export type { BlobRef, CreateBlobRefArgs } from "./shared/lib/blob-ref";
export { computeBlobHash, createBlobRef, isBlobRef } from "./shared/lib/blob-ref";
// Runtime constraint checking
export {
  checkPostconditions,
  checkPreconditions,
  clearConstraints,
  isRuntimeConstraintsEnabled,
  registerConstraint,
  registerConstraints,
} from "./shared/lib/constraints";
export type { ContextConfig } from "./shared/lib/context-helpers";
// Context helpers (DX improvements)
export { createContext, runInContext } from "./shared/lib/context-helpers";
// Context-specific helpers (DX improvements)
export type {
  BackgroundHelpers,
  ContentScriptHelpers,
  DevToolsHelpers,
  OptionsHelpers,
  PopupHelpers,
  SidePanelHelpers,
} from "./shared/lib/context-specific-helpers";
export type {
  CounterDoc,
  CrdtCounterOptions,
  CrdtListOptions,
  CrdtTextOptions,
  ListDoc,
  SpecialisedPrimitive,
  TextDoc,
} from "./shared/lib/crdt-specialised";
export { $crdtCounter, $crdtList, $crdtText } from "./shared/lib/crdt-specialised";
export type { CrdtPrimitive, CrdtStateOptions } from "./shared/lib/crdt-state";
export { $crdtState } from "./shared/lib/crdt-state";
// Phase 2 — $meshState wrappers and the cryptographic transport that
// underlies them. The MeshNetworkAdapter wraps any base NetworkAdapter
// with sign-then-encrypt envelopes; signing.ts and encryption.ts expose
// the underlying tweetnacl primitives via a Polly-flavoured API so
// application code never imports tweetnacl directly.
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
// Errors
export {
  ConnectionError,
  ErrorHandler,
  ExtensionError,
  HandlerError,
  TimeoutError,
} from "./shared/lib/errors";
export type {
  MeshKeyring,
  MeshNetworkAdapterOptions,
} from "./shared/lib/mesh-network-adapter";
export {
  DEFAULT_MESH_KEY_ID,
  MeshNetworkAdapter,
} from "./shared/lib/mesh-network-adapter";
export type { MeshStateOptions } from "./shared/lib/mesh-state";
export {
  $meshCounter,
  $meshList,
  $meshState,
  $meshText,
  configureMeshState,
  resetMeshState,
} from "./shared/lib/mesh-state";
// Messaging
export { getMessageBus, MessageBus } from "./shared/lib/message-bus";
export type { MigratableState } from "./shared/lib/migrate-primitive";
export { MigrationError, migratePrimitive } from "./shared/lib/migrate-primitive";
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
// Phase 1 — $peerState wrappers around the base $crdt* family with the
// peerState primitive kind, key→DocumentId mapping per Repo, and the
// deferred-crypto encrypt/sign options that throw at runtime until Phase 2.
export type {
  CreatePeerStateClientOptions,
  PeerRelayConnectionState,
  PeerStateClient,
} from "./shared/lib/peer-relay-adapter";
export { createPeerStateClient } from "./shared/lib/peer-relay-adapter";
export type {
  CreatePeerRepoServerOptions,
  PeerRepoServer,
} from "./shared/lib/peer-repo-server";
export { createPeerRepoServer } from "./shared/lib/peer-repo-server";
export type {
  PeerCounterOptions,
  PeerListOptions,
  PeerStateOptions,
  PeerTextOptions,
} from "./shared/lib/peer-state";
export {
  $peerCounter,
  $peerList,
  $peerState,
  $peerText,
  configurePeerState,
  resetPeerState,
} from "./shared/lib/peer-state";
export type { PrimitiveKind } from "./shared/lib/primitive-registry";
export { PrimitiveCollisionError } from "./shared/lib/primitive-registry";
export type { Resource, ResourceOptions, ResourceStatus } from "./shared/lib/resource";
// Async resource primitive
export { $resource } from "./shared/lib/resource";
export type {
  Migration,
  Migrations,
  OpVersionCheck,
  VersionedDoc,
} from "./shared/lib/schema-version";
export {
  assertOpVersion,
  checkOpVersion,
  getDocVersion,
  SCHEMA_VERSION_FIELD,
  SchemaVersionError,
} from "./shared/lib/schema-version";
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
// State management
export { $persistedState, $sharedState, $state, $syncedState } from "./shared/lib/state";

export type { TestCase, TestSuite } from "./shared/lib/test-helpers";
// Test utilities (DX improvements)
export { createTestSuite, quickTest, TestRunner } from "./shared/lib/test-helpers";
// Validation helpers
export {
  validateArray,
  validateEnum,
  validatePartial,
  validateShape,
} from "./shared/lib/validation";
export { settings } from "./shared/state/app-state";

// Types
export type {
  Context,
  ExtensionMessage,
  MessageResponse,
  RoutedMessage,
  RoutedResponse,
  Settings,
} from "./shared/types/messages";
