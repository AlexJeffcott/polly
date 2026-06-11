/**
 * Central factories for automerge-repo's branded string types.
 *
 * `PeerId` and `DocumentId` are nominal (branded) string types with no
 * runtime constructor, so a test that wants `"peer-a"` as a `PeerId` has
 * no choice but to cast. The no-as-casting gate's instruction for that
 * case is to centralise the cast in a factory — this module is that
 * factory. Tests import `peerId("peer-a")` instead of scattering
 * `"peer-a" as PeerId` casts, so the deliberate unsoundness lives in
 * exactly one greppable place.
 */

import type { DocumentId, PeerId } from "@automerge/automerge-repo";

/** Brand a string as a PeerId for test wiring. */
export function peerId(id: string): PeerId {
  return id as unknown as PeerId;
}

/** Brand a string as a DocumentId for test wiring. */
export function documentId(id: string): DocumentId {
  return id as unknown as DocumentId;
}
