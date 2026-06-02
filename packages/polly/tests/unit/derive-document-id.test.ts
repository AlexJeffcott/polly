/**
 * Tests for deriveDocumentId — the domain-separated SHA-512 derivation that
 * maps a logical $meshState key to a 16-byte Automerge DocumentId.
 *
 * The derivation is the wire contract two peers must agree on byte-for-byte
 * to land on the same document, so the tests pin the exact recipe (domain
 * prefix, ":" separator, first-16-bytes slice) by recomputing it
 * independently and asserting equality, plus the determinism and
 * key-sensitivity the mesh relies on.
 */

import { describe, expect, test } from "bun:test";
import { type BinaryDocumentId, interpretAsDocumentId } from "@automerge/automerge-repo/slim";
import nacl from "tweetnacl";
import { deriveDocumentId } from "@/shared/lib/derive-document-id";

/** Recompute the expected id straight from the documented recipe, so a
 * mutated domain prefix, separator, or slice length in the implementation
 * diverges from this and fails the assertion. */
function expectedId(key: string): string {
  const digest = nacl.hash(new TextEncoder().encode(`polly/meshState/v1:${key}`));
  return interpretAsDocumentId(digest.slice(0, 16) as unknown as BinaryDocumentId);
}

describe("deriveDocumentId", () => {
  test("matches the domain-separated SHA-512 first-16-bytes recipe", () => {
    expect(deriveDocumentId("inbox")).toBe(expectedId("inbox"));
  });

  test("is deterministic for the same key", () => {
    expect(deriveDocumentId("contacts")).toBe(deriveDocumentId("contacts"));
  });

  test("produces distinct ids for distinct keys", () => {
    expect(deriveDocumentId("alpha")).not.toBe(deriveDocumentId("beta"));
  });

  test("is sensitive to the key beyond a shared prefix", () => {
    // The full key feeds the hash, so neither truncation nor a shared prefix
    // collapses two different keys onto one document.
    expect(deriveDocumentId("doc")).not.toBe(deriveDocumentId("doc:v2"));
    expect(deriveDocumentId("a")).not.toBe(deriveDocumentId("ab"));
  });

  test("handles an empty key via the same recipe", () => {
    expect(deriveDocumentId("")).toBe(expectedId(""));
  });

  test("derives a non-empty DocumentId string", () => {
    const id = deriveDocumentId("inbox");
    expect(typeof id).toBe("string");
    expect(id.length).toBeGreaterThan(0);
  });
});
