/**
 * Unit tests for the RFC-043 revocation decision cores on mesh-client
 * (polly#124). These were closure-captured inside createMeshClient and so
 * NoCoverage in the unit suite; they are now module-level pure functions
 * pinned directly through the __test__ seam:
 *
 *   - shouldReplaceRevocation / storeRevocationInto — last-write-wins store
 *   - revocationsMissingFromSummary — the gossip diff that converges two peers
 *   - classifyIncomingRevocation — self / duplicate / apply
 *
 * Hand-built stubs only; no real keyring, network adapter, or client.
 */
import { describe, expect, test } from "bun:test";
import { __test__ } from "@/shared/lib/mesh-client";
import type { RevocationRecord } from "@/shared/lib/revocation";
import type { RevocationSummaryEntry } from "@/shared/lib/revocation-summary";

const {
  storeRevocationInto,
  shouldReplaceRevocation,
  revocationsMissingFromSummary,
  classifyIncomingRevocation,
} = __test__;

type Store = Map<string, { bytes: Uint8Array; entry: RevocationSummaryEntry }>;

function makeRecord(overrides: {
  revokedPeerId: string;
  issuerPeerId?: string;
  issuedAt: number;
}): RevocationRecord {
  return {
    version: 1,
    revokedPeerId: overrides.revokedPeerId,
    issuerPeerId: overrides.issuerPeerId ?? "issuer",
    issuedAt: overrides.issuedAt,
  };
}

describe("shouldReplaceRevocation / storeRevocationInto — last-write-wins (#124)", () => {
  test("first write into an empty store is stored", () => {
    const store: Store = new Map();
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 100 }),
      new Uint8Array([1])
    );
    expect(store.get("A")?.entry.issuedAt).toBe(100);
    expect([...(store.get("A")?.bytes ?? [])]).toEqual([1]);
  });

  test("a newer issuedAt replaces the older record", () => {
    const store: Store = new Map();
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 100 }),
      new Uint8Array([1])
    );
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 200 }),
      new Uint8Array([2])
    );
    expect(store.get("A")?.entry.issuedAt).toBe(200);
    expect([...(store.get("A")?.bytes ?? [])]).toEqual([2]);
  });

  test("an older issuedAt does NOT replace the newer record (kills >=/< flips)", () => {
    const store: Store = new Map();
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 200 }),
      new Uint8Array([2])
    );
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 100 }),
      new Uint8Array([1])
    );
    expect(store.get("A")?.entry.issuedAt).toBe(200);
    expect([...(store.get("A")?.bytes ?? [])]).toEqual([2]);
  });

  test("an equal issuedAt does NOT replace — the first write wins (kills > → >=)", () => {
    const store: Store = new Map();
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 150 }),
      new Uint8Array([1])
    );
    storeRevocationInto(
      store,
      makeRecord({ revokedPeerId: "A", issuedAt: 150 }),
      new Uint8Array([9])
    );
    // Strict newer-than: an equal-timestamp write must not overwrite.
    expect([...(store.get("A")?.bytes ?? [])]).toEqual([1]);
  });

  test("shouldReplaceRevocation is true only when absent or strictly newer", () => {
    const existing = {
      bytes: new Uint8Array(),
      entry: { revokedPeerId: "A", issuerPeerId: "i", issuedAt: 100 },
    };
    expect(
      shouldReplaceRevocation(undefined, makeRecord({ revokedPeerId: "A", issuedAt: 1 }))
    ).toBe(true);
    expect(
      shouldReplaceRevocation(existing, makeRecord({ revokedPeerId: "A", issuedAt: 101 }))
    ).toBe(true);
    expect(
      shouldReplaceRevocation(existing, makeRecord({ revokedPeerId: "A", issuedAt: 100 }))
    ).toBe(false);
    expect(
      shouldReplaceRevocation(existing, makeRecord({ revokedPeerId: "A", issuedAt: 99 }))
    ).toBe(false);
  });
});

describe("revocationsMissingFromSummary — gossip diff (#124)", () => {
  function storeOf(ids: string[]): Store {
    const store: Store = new Map();
    for (const id of ids) {
      store.set(id, {
        bytes: new Uint8Array([id.charCodeAt(0)]),
        entry: { revokedPeerId: id, issuerPeerId: "issuer", issuedAt: 1 },
      });
    }
    return store;
  }
  const summaryEntry = (
    revokedPeerId: string,
    issuerPeerId = "issuer"
  ): RevocationSummaryEntry => ({
    revokedPeerId,
    issuerPeerId,
    issuedAt: 1,
  });

  test("returns bytes for stored revocations absent from the remote summary", () => {
    const missing = revocationsMissingFromSummary(storeOf(["A", "B", "C"]), [summaryEntry("B")]);
    const got = missing.map((b) => b[0]).sort();
    expect(got).toEqual(["A".charCodeAt(0), "C".charCodeAt(0)].sort());
  });

  test("returns empty when the summary already covers every stored revocation", () => {
    const missing = revocationsMissingFromSummary(storeOf(["A", "B"]), [
      summaryEntry("A"),
      summaryEntry("B"),
    ]);
    expect(missing).toEqual([]);
  });

  test("returns ALL stored bytes when the summary is empty", () => {
    const missing = revocationsMissingFromSummary(storeOf(["A", "B"]), []);
    expect(missing.map((b) => b[0]).sort()).toEqual(["A".charCodeAt(0), "B".charCodeAt(0)].sort());
  });

  test("membership is keyed by revokedPeerId, not issuerPeerId", () => {
    // Summary covers revokedPeerId A but lists a different issuer; A is still
    // considered present and must be excluded.
    const missing = revocationsMissingFromSummary(storeOf(["A"]), [
      summaryEntry("A", "someone-else"),
    ]);
    expect(missing).toEqual([]);
  });
});

describe("classifyIncomingRevocation — three-way branch (#124)", () => {
  test("self when revokedPeerId === localPeerId", () => {
    const r = makeRecord({ revokedPeerId: "me", issuedAt: 1 });
    expect(classifyIncomingRevocation(r, "me", new Set())).toBe("self");
  });

  test("self takes precedence even when the id is also in revokedPeers", () => {
    const r = makeRecord({ revokedPeerId: "me", issuedAt: 1 });
    expect(classifyIncomingRevocation(r, "me", new Set(["me"]))).toBe("self");
  });

  test("duplicate when already in revokedPeers and not self", () => {
    const r = makeRecord({ revokedPeerId: "X", issuedAt: 1 });
    expect(classifyIncomingRevocation(r, "me", new Set(["X"]))).toBe("duplicate");
  });

  test("apply when neither self nor known", () => {
    const r = makeRecord({ revokedPeerId: "X", issuedAt: 1 });
    expect(classifyIncomingRevocation(r, "me", new Set())).toBe("apply");
  });
});
