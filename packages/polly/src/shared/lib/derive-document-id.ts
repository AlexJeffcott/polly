/**
 * Leaf module for {@link deriveDocumentId}. Kept free of the wider
 * `mesh-state` module graph (CRDT primitives, the Repo, schema
 * migrations) so that importing it does not pull the whole mesh runtime
 * in. `mesh-state` re-exports it, so consumer-facing imports are
 * unchanged. The derivation itself is in {@link ./derive-document-id-core},
 * which `polly visualize` (polly#127) calls with lazily loaded primitives.
 */

import { type DocumentId, interpretAsDocumentId } from "@automerge/automerge-repo/slim";
import nacl from "tweetnacl";
import { deriveDocumentIdWith } from "./derive-document-id-core";

/**
 * Domain-separated hash of an application key into a 16-byte
 * {@link DocumentId}. SHA-512 via tweetnacl (already a dep for
 * signing); the first 16 bytes give a DocumentId with uniform
 * distribution across the Automerge id space.
 *
 * Exported so consumers can compute the derived id for any logical key
 * — useful for ADR 0008-style document compaction where the consumer
 * wants to seed a new doc at `deriveDocumentId(key + ':v' + timestamp)`
 * and stash that id in a runtime index.
 */
export function deriveDocumentId(key: string): DocumentId {
  return deriveDocumentIdWith({ hash: nacl.hash, interpretAsDocumentId }, key);
}
