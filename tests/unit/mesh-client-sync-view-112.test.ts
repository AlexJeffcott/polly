/**
 * Unit tests for the polly#112 diagnostic structural reader.
 *
 * `buildSyncView` lifts per-(docId, peerId) state off Automerge's
 * hidden `CollectionSynchronizer` — `hasPeer()` and `peerStates` —
 * so {@link MeshClient.getPeerStateSnapshot} can surface the wedged
 * pair fingerprint #112 reports: a handle whose docSynchronizer
 * exists but never registered the peer, or registered the peer but
 * left its `peerDocumentStatus` at `"unknown"` after the opening
 * handshake.
 *
 * These tests exercise the reader against hand-built stubs so the
 * shape contract is locked down without spinning up a real Repo.
 * End-to-end coverage of the actual stall lives in fairfox's
 * `scripts/e2e-user-revocation.ts`.
 */

import { describe, expect, test } from "bun:test";
import { __test__ } from "@/shared/lib/mesh-client";

const { buildSyncView, EMPTY_SYNC_VIEW } = __test__;

describe("buildSyncView (#112 diagnostic)", () => {
  test("no synchronizer returns the empty view", () => {
    const view = buildSyncView(undefined, "doc-A", "peer-1");
    expect(view).toEqual(EMPTY_SYNC_VIEW);
    expect(view.docSynchronizerExists).toBe(false);
  });

  test("synchronizer present but no docSynchronizer for this doc", () => {
    const view = buildSyncView({ docSynchronizers: {} }, "doc-A", "peer-1");
    expect(view.docSynchronizerExists).toBe(false);
    expect(view.docSynchronizerKnowsPeer).toBeUndefined();
    expect(view.peerDocumentStatus).toBeUndefined();
  });

  test("docSynchronizer present, peer registered, status 'has' — the healthy fingerprint", () => {
    const view = buildSyncView(
      {
        docSynchronizers: {
          "doc-A": {
            hasPeer: (p) => p === "peer-1",
            peerStates: { "peer-1": "has" },
          },
        },
      },
      "doc-A",
      "peer-1"
    );
    expect(view.docSynchronizerExists).toBe(true);
    expect(view.docSynchronizerKnowsPeer).toBe(true);
    expect(view.peerDocumentStatus).toBe("has");
  });

  test("docSynchronizer present, peer registered, status 'unknown' — the wedged-pair fingerprint", () => {
    // This is the #112 smoking gun when paired with
    // `lastSyncMessageOutAt !== undefined`: the opening sync message
    // went out, the docSynchronizer knows the peer, but
    // generateSyncMessage never advanced past the handshake.
    const view = buildSyncView(
      {
        docSynchronizers: {
          "mesh:users-docid": {
            hasPeer: (p) => p === "phone",
            peerStates: { phone: "unknown" },
          },
        },
      },
      "mesh:users-docid",
      "phone"
    );
    expect(view.docSynchronizerExists).toBe(true);
    expect(view.docSynchronizerKnowsPeer).toBe(true);
    expect(view.peerDocumentStatus).toBe("unknown");
  });

  test("docSynchronizer present, peer NOT registered — the symmetric polly#107 gap", () => {
    // Handle was created after `peer-candidate` fired and Automerge's
    // `addDocument`-iterates-peers path never picked the peer up.
    const view = buildSyncView(
      {
        docSynchronizers: {
          "doc-A": {
            hasPeer: () => false,
            peerStates: {},
          },
        },
      },
      "doc-A",
      "peer-1"
    );
    expect(view.docSynchronizerExists).toBe(true);
    expect(view.docSynchronizerKnowsPeer).toBe(false);
    expect(view.peerDocumentStatus).toBeUndefined();
  });

  test("hasPeer throws — read degrades to undefined, doesn't crash the snapshot", () => {
    const view = buildSyncView(
      {
        docSynchronizers: {
          "doc-A": {
            hasPeer: () => {
              throw new Error("boom");
            },
            peerStates: { "peer-1": "has" },
          },
        },
      },
      "doc-A",
      "peer-1"
    );
    expect(view.docSynchronizerExists).toBe(true);
    expect(view.docSynchronizerKnowsPeer).toBeUndefined();
    expect(view.peerDocumentStatus).toBe("has");
  });

  test("peerStates missing entirely — read degrades to undefined", () => {
    const view = buildSyncView(
      {
        docSynchronizers: {
          "doc-A": {
            hasPeer: () => true,
          },
        },
      },
      "doc-A",
      "peer-1"
    );
    expect(view.docSynchronizerExists).toBe(true);
    expect(view.docSynchronizerKnowsPeer).toBe(true);
    expect(view.peerDocumentStatus).toBeUndefined();
  });
});
