/**
 * Constructors for automerge-repo's branded string types.
 *
 * `PeerId`, `DocumentId` and `StorageId` are `string & { __brand }` with no
 * runtime constructor, so a cast is the only way to make one. The casts live
 * here, once each; everything else calls these.
 */

import type { DocumentId, PeerId, StorageId } from "@automerge/automerge-repo/slim";

export function toPeerId(id: string): PeerId {
  // cast: PeerId has no constructor; a peer id is any string
  return id as PeerId;
}

export function toDocumentId(id: string): DocumentId {
  // cast: DocumentId has no constructor; callers pass an id automerge-repo issued
  return id as DocumentId;
}

export function toStorageId(id: string): StorageId {
  // cast: StorageId has no constructor; a storage id is any string
  return id as StorageId;
}
