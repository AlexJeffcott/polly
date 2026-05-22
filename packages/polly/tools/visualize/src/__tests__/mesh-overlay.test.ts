/**
 * polly#127: the visualiser overlays a captured runtime
 * `MeshClientPeerStateSnapshot` onto the static architecture diagram.
 *
 * Runs the real ArchitectureAnalyzer over the mesh-app fixture, loads
 * the committed snapshot through the documented loader, and asserts the
 * generated DSL carries synthesised peer nodes and status-coloured
 * replication edges — and that, without a snapshot, the DSL is
 * unchanged.
 */

import { describe, expect, test } from "bun:test";
import path from "node:path";
import { ArchitectureAnalyzer } from "../../../analysis/src/extract/architecture";
import type { ArchitectureAnalysis } from "../../../analysis/src/types/architecture";
import { generateStructurizrDSL } from "../codegen/structurizr";
import {
  collectSnapshotPeerIds,
  loadMeshSnapshot,
  MeshSnapshotError,
  validateMeshSnapshot,
} from "../mesh-snapshot";

const projectRoot = path.join(__dirname, "fixtures/mesh-app");
const snapshotPath = path.join(projectRoot, "snapshot.json");

const analysis: ArchitectureAnalysis = await new ArchitectureAnalyzer({
  tsConfigPath: path.join(projectRoot, "tsconfig.json"),
  projectRoot,
}).analyze();

const snapshot = loadMeshSnapshot(snapshotPath);
const overlayDsl = generateStructurizrDSL(analysis, { snapshot });

describe("mesh sync-state overlay (polly#127)", () => {
  test("synthesises one person node per snapshot peer", () => {
    expect(overlayDsl).toContain('person "peer-local-7c1d" "Local mesh peer (this node)"');
    expect(overlayDsl).toContain('person "peer-aa11" "Runtime mesh peer"');
    expect(overlayDsl).toContain('person "peer-bb22" "Runtime mesh peer"');
    expect(overlayDsl).toContain('person "peer-cc33" "Runtime mesh peer"');
  });

  test("tags the local peer distinctly from remote peers", () => {
    // The local peer carries the Local tag; remote peers the plain one.
    expect(overlayDsl).toMatch(/person "peer-local-7c1d"[^}]*tags "Local Mesh Peer"/);
    expect(overlayDsl).toMatch(/person "peer-aa11"[^}]*tags "Mesh Peer"/);
  });

  test("overlays a coloured edge onto the matching static mesh document", () => {
    // deriveDocumentId('chat-rooms') resolves the snapshot handle key
    // back to the static mesh_doc_chat_rooms node.
    expect(overlayDsl).toMatch(/-> extension\.mesh_doc_chat_rooms "has" \{\s*tags "sync:has"/);
    expect(overlayDsl).toMatch(
      /-> extension\.mesh_doc_chat_presence "wants" \{\s*tags "sync:wants"/
    );
  });

  test("the edge label reflects the #112 synchronizer diagnostics", () => {
    // docSynchronizerKnowsPeer false -> "peer not added"; a missing
    // docSynchronizer -> "no synchronizer".
    expect(overlayDsl).toContain('"unavailable · peer not added"');
    expect(overlayDsl).toContain('"unknown · no synchronizer"');
  });

  test("renders a snapshot-only node for a docId static analysis missed", () => {
    expect(overlayDsl).toContain("3WvsPq9LxKmNbHgTfRcDaEuY7zJ2");
    expect(overlayDsl).toMatch(/mesh_doc_3wvspq9lxkmnbhgtfrcdaeuy7zj2 = container/);
    expect(overlayDsl).toMatch(
      /mesh_doc_3wvspq9lxkmnbhgtfrcdaeuy7zj2 = container[\s\S]*?tags "Snapshot Document"/
    );
    expect(overlayDsl).toMatch(
      /-> extension\.mesh_doc_3wvspq9lxkmnbhgtfrcdaeuy7zj2 "unknown · no synchronizer" \{\s*tags "sync:unknown"/
    );
  });

  test("a peer with no slot is rendered with no document edges", () => {
    expect(overlayDsl).toContain('person "peer-cc33"');
    // peer-cc33 -> ... never appears: its slot is absent.
    expect(overlayDsl).not.toMatch(/peer_peer_cc33 ->/);
  });

  test("the styles block colours each peerDocumentStatus distinctly", () => {
    for (const status of ["sync:has", "sync:wants", "sync:unavailable", "sync:unknown"]) {
      expect(overlayDsl).toContain(`relationship "${status}"`);
    }
    expect(overlayDsl).toMatch(/relationship "sync:has"[^}]*color #2f9e44/);
    expect(overlayDsl).toMatch(/relationship "sync:unavailable"[^}]*color #e03131/);
    expect(overlayDsl).toContain('element "Mesh Peer"');
    expect(overlayDsl).toContain('element "Local Mesh Peer"');
    expect(overlayDsl).toContain('element "Snapshot Document"');
  });

  test("without a snapshot the DSL carries no overlay artefacts", () => {
    const staticDsl = generateStructurizrDSL(analysis);
    expect(staticDsl).not.toContain("sync:");
    expect(staticDsl).not.toContain("Mesh Peer");
    expect(staticDsl).not.toContain("Snapshot Document");
    expect(staticDsl).not.toMatch(/= person "peer-/);
    // Passing `snapshot: undefined` explicitly must behave identically
    // to omitting it — the CLI does this on the no-snapshot path.
    expect(generateStructurizrDSL(analysis, { snapshot: undefined })).toBe(staticDsl);
  });
});

describe("mesh snapshot loader (polly#127)", () => {
  test("collectSnapshotPeerIds unions local, roster, and peers[]", () => {
    expect(collectSnapshotPeerIds(snapshot).sort()).toEqual([
      "peer-aa11",
      "peer-bb22",
      "peer-cc33",
      "peer-local-7c1d",
    ]);
  });

  test("rejects a missing file with a clear error", () => {
    expect(() => loadMeshSnapshot(path.join(projectRoot, "does-not-exist.json"))).toThrow(
      MeshSnapshotError
    );
  });

  test("rejects a non-object snapshot", () => {
    expect(() => validateMeshSnapshot([])).toThrow(/must be a JSON object/);
  });

  test("rejects a snapshot missing localPeerId", () => {
    expect(() => validateMeshSnapshot({ knownPeerIds: [], presentPeerIds: [], peers: [] })).toThrow(
      /localPeerId/
    );
  });

  test("rejects a handle with a non-boolean docSynchronizerExists", () => {
    expect(() =>
      validateMeshSnapshot({
        localPeerId: "p0",
        knownPeerIds: [],
        presentPeerIds: [],
        peers: [
          {
            peerId: "p1",
            slot: { handles: { doc1: { docSynchronizerExists: "yes" } } },
          },
        ],
      })
    ).toThrow(/docSynchronizerExists/);
  });

  test("accepts a peer whose slot is absent", () => {
    const ok = validateMeshSnapshot({
      localPeerId: "p0",
      knownPeerIds: ["p1"],
      presentPeerIds: [],
      peers: [{ peerId: "p1" }],
    });
    expect(ok.peers[0]?.peerId).toBe("p1");
  });
});
