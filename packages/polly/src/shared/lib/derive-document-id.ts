/**
 * Leaf module for {@link deriveDocumentId}. Kept free of the wider
 * `mesh-state` module graph (CRDT primitives, the Repo, schema
 * migrations) so that tooling — notably `polly visualize` (polly#127) —
 * can resolve a logical key to its {@link DocumentId} without pulling
 * the whole mesh runtime into its bundle. `mesh-state` re-exports it,
 * so consumer-facing imports are unchanged.
 */

import {
  type BinaryDocumentId,
  type DocumentId,
  interpretAsDocumentId,
} from "@automerge/automerge-repo/slim";
import nacl from "tweetnacl";

/** Domain prefix pinning the derivation to $meshState so that the same
 * logical key used in a different Polly subsystem would produce a
 * different id. */
const DOC_ID_DOMAIN = "polly/meshState/v1";
const keyEncoder = new TextEncoder();

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
  const digest = nacl.hash(keyEncoder.encode(`${DOC_ID_DOMAIN}:${key}`));
  const bytes = digest.slice(0, 16);
  return interpretAsDocumentId(bytes as unknown as BinaryDocumentId);
}
