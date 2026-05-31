/**
 * Unit tests for the polly#107 snapshot-enrichment helpers on mesh-client:
 * enrichPeerSlot (which merges Repo handle state, adapter wire timestamps, and
 * the #112 docSynchronizer view into each per-handle entry), stringifyHandleState,
 * and getCollectionSynchronizer.
 *
 * The sibling sync-view test already pins buildSyncView; mutation testing
 * showed the merge/coercion layer around it was executed but unasserted
 * (theatre). These tests pin the derived fields directly through the
 * __test__ seam.
 */
import { describe, expect, test } from "bun:test";
import { __test__ } from "@/shared/lib/mesh-client";

const { enrichPeerSlot, getCollectionSynchronizer } = __test__;

type Any = ReturnType<typeof JSON.parse>;

const fullWire = {
  lastSyncMessageOutAt: 100,
  lastSyncMessageInAt: 90,
  lastSyncMessageOutSize: 42,
  lastSyncMessageOutType: "sync",
};
const emptyWire = {
  lastSyncMessageOutAt: undefined,
  lastSyncMessageInAt: undefined,
  lastSyncMessageOutSize: undefined,
  lastSyncMessageOutType: undefined,
};

function peerWith(handles: Record<string, unknown>): Any {
  return { peerId: "peer-1", slot: { handles } };
}

describe("enrichPeerSlot — wire + state merge", () => {
  test("merges the wire timestamps and repo state into the handle entry", () => {
    const out = enrichPeerSlot(
      peerWith({ "doc-A": fullWire }),
      ["doc-A"],
      { "doc-A": { state: "ready" } },
      undefined
    );
    const h = (out.slot as Any).handles["doc-A"];
    expect(h.state).toBe("ready");
    expect(h.announcedToPeer).toBe(true);
    expect(h.lastSyncMessageOutAt).toBe(100);
    expect(h.lastSyncMessageInAt).toBe(90);
    expect(h.lastSyncMessageOutSize).toBe(42);
    expect(h.lastSyncMessageOutType).toBe("sync");
  });

  test("announcedToPeer is false when no outgoing sync has been sent", () => {
    const out = enrichPeerSlot(
      peerWith({ "doc-A": emptyWire }),
      ["doc-A"],
      { "doc-A": { state: "ready" } },
      undefined
    );
    expect((out.slot as Any).handles["doc-A"].announcedToPeer).toBe(false);
  });

  test("a known handle absent from the slot yields unknown state and no wire data", () => {
    // doc-A is a known handle id but the peer's slot has no entry for it, and
    // the repo has no handle either: stringifyHandleState(undefined) → "unknown"
    // and buildHandleEntry must tolerate an undefined wire.
    const out = enrichPeerSlot(peerWith({}), ["doc-A"], {}, undefined);
    const h = (out.slot as Any).handles["doc-A"];
    expect(h.state).toBe("unknown");
    expect(h.announcedToPeer).toBe(false);
    expect(h.lastSyncMessageOutAt).toBeUndefined();
  });

  test("enriches handles present in the slot even when not in knownHandleIds", () => {
    const out = enrichPeerSlot(peerWith({ "doc-B": fullWire }), [], {}, undefined);
    const h = (out.slot as Any).handles["doc-B"];
    expect(h).toBeDefined();
    expect(h.state).toBe("unknown");
    expect(h.lastSyncMessageOutAt).toBe(100);
  });

  test("wires the #112 docSynchronizer view through buildSyncView", () => {
    const synchronizer = {
      docSynchronizers: {
        "doc-A": { hasPeer: (p: string) => p === "peer-1", peerStates: { "peer-1": "has" } },
      },
    };
    const out = enrichPeerSlot(
      peerWith({ "doc-A": fullWire }),
      ["doc-A"],
      { "doc-A": { state: "ready" } },
      synchronizer as Any
    );
    const h = (out.slot as Any).handles["doc-A"];
    expect(h.docSynchronizerExists).toBe(true);
    expect(h.docSynchronizerKnowsPeer).toBe(true);
    expect(h.peerDocumentStatus).toBe("has");
  });

  test("a peer with no slot is returned with slot undefined", () => {
    const out = enrichPeerSlot(
      { peerId: "peer-1", slot: undefined } as Any,
      ["doc-A"],
      {},
      undefined
    );
    expect(out.slot).toBeUndefined();
  });
});

describe("stringifyHandleState (via enrichPeerSlot)", () => {
  function stateOf(repoHandle: unknown): string {
    const out = enrichPeerSlot(
      peerWith({ "doc-A": fullWire }),
      ["doc-A"],
      { "doc-A": repoHandle as Any },
      undefined
    );
    return (out.slot as Any).handles["doc-A"].state;
  }

  test("returns a string state verbatim", () => {
    expect(stateOf({ state: "ready" })).toBe("ready");
  });

  test("coerces a non-string state to a string", () => {
    expect(stateOf({ state: 123 })).toBe("123");
  });

  test("falls back to 'unknown' for a nullish state", () => {
    expect(stateOf({ state: undefined })).toBe("unknown");
  });
});

describe("getCollectionSynchronizer", () => {
  test("returns the synchronizer object off the repo", () => {
    const synchronizer = { docSynchronizers: {} };
    expect(getCollectionSynchronizer({ synchronizer } as Any)).toBe(synchronizer);
  });

  test("returns undefined when the repo exposes no synchronizer", () => {
    expect(getCollectionSynchronizer({} as Any)).toBeUndefined();
  });

  test("returns undefined when the synchronizer is truthy but not an object", () => {
    // Guards the `&& typeof sync === "object"` half: a function is truthy.
    expect(getCollectionSynchronizer({ synchronizer: (() => {}) as Any } as Any)).toBeUndefined();
  });
});
