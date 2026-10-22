/**
 * Test names for the branded-type constructors in `src/shared/lib/branded.ts`.
 * Tests import `peerId("peer-a")` instead of casting `"peer-a" as PeerId`.
 */

export {
  toDocumentId as documentId,
  toPeerId as peerId,
  toStorageId as storageId,
} from "../../../src/shared/lib/branded";
