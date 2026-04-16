/**
 * @fairfox/polly/peer — peer-first CRDT state primitives.
 *
 * Automerge-backed reactive state that syncs via a relay server.
 * This subpath export isolates the @automerge/* dependency tree so
 * consumers who only use $sharedState / $syncedState / $resource
 * never pull in automerge.
 *
 * @example
 * ```typescript
 * import { $peerState, configurePeerState } from "@fairfox/polly/peer";
 * ```
 */

// Base CRDT primitives (transport-agnostic, caller-supplied handle factory)
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

// Peer-state wrappers (key→DocumentId mapping per Repo, relay transport)
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

// Relay adapter and server
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

// Primitive registry (needed for CRDT primitive kinds)
export type { PrimitiveKind } from "./shared/lib/primitive-registry";
export { PrimitiveCollisionError } from "./shared/lib/primitive-registry";

// Migration support (needed for CRDT schema versioning)
export type { MigratableState } from "./shared/lib/migrate-primitive";
export { MigrationError, migratePrimitive } from "./shared/lib/migrate-primitive";
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
