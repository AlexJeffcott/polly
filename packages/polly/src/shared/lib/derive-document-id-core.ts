/**
 * The derivation behind {@link ./derive-document-id}, with its two
 * primitives passed in rather than imported. It imports only types, so
 * it loads without `tweetnacl` or `@automerge/automerge-repo`.
 *
 * `polly visualize` needs the derived id only to overlay a `--snapshot`
 * (polly#127). It loads the two optional peers with a dynamic import when
 * a snapshot is given and calls this, so a plain `polly visualize` runs
 * without them. `deriveDocumentId` calls this with the statically
 * imported primitives, so both paths share one derivation.
 */

import type { BinaryDocumentId, DocumentId } from "@automerge/automerge-repo/slim";

/** Domain prefix pinning the derivation to $meshState so that the same
 * logical key used in a different Polly subsystem would produce a
 * different id. */
const DOC_ID_DOMAIN = "polly/meshState/v1";
const keyEncoder = new TextEncoder();

/** The two primitives the derivation uses: tweetnacl's SHA-512 and automerge-repo's id encoder. */
export interface DocumentIdPrimitives {
  hash: (message: Uint8Array) => Uint8Array;
  interpretAsDocumentId: (id: BinaryDocumentId) => DocumentId;
}

/**
 * Domain-separated hash of an application key into a 16-byte
 * {@link DocumentId}: the first 16 bytes of SHA-512 give a DocumentId with
 * uniform distribution across the Automerge id space.
 */
export function deriveDocumentIdWith(primitives: DocumentIdPrimitives, key: string): DocumentId {
  const digest = primitives.hash(keyEncoder.encode(`${DOC_ID_DOMAIN}:${key}`));
  const bytes = digest.slice(0, 16);
  return primitives.interpretAsDocumentId(bytes as unknown as BinaryDocumentId);
}
