/**
 * polly#114: the visualiser renders $meshState / $peerState documents as
 * first-class nodes.
 *
 * Runs the real ArchitectureAnalyzer over the mesh-app fixture, then the
 * DSL generator, and asserts the mesh documents reach the diagram as
 * tagged containers with an edge from the context that declares them.
 */

import { describe, expect, test } from "bun:test";
import path from "node:path";
import { ArchitectureAnalyzer } from "../../../analysis/src/extract/architecture";
import type { ArchitectureAnalysis } from "../../../analysis/src/types/architecture";
import { generateStructurizrDSL } from "../codegen/structurizr";

const projectRoot = path.join(__dirname, "fixtures/mesh-app");

const analysis: ArchitectureAnalysis = await new ArchitectureAnalyzer({
  tsConfigPath: path.join(projectRoot, "tsconfig.json"),
  projectRoot,
}).analyze();

describe("mesh primitives in the architecture diagram (polly#114)", () => {
  test("analysis discovers both $meshState documents", () => {
    const keys = (analysis.meshOrPeerSignals ?? [])
      .filter((s) => s.kind === "mesh")
      .map((s) => s.key)
      .sort();
    expect(keys).toEqual(["chat-presence", "chat-rooms"]);
  });

  test("the DSL emits each mesh document as a tagged container", () => {
    const dsl = generateStructurizrDSL(analysis);
    expect(dsl).toContain("mesh_doc_chat_rooms = container");
    expect(dsl).toContain("mesh_doc_chat_presence = container");
    expect(dsl).toContain('tags "Mesh Document"');
    expect(dsl).toContain("$meshState");
    // The resolved-docId symbol is carried on the node's label.
    expect(dsl).toContain("deriveDocumentId('chat-rooms')");
  });

  test("the DSL draws an edge from the context to each mesh document", () => {
    const dsl = generateStructurizrDSL(analysis);
    expect(dsl).toMatch(/-> extension\.mesh_doc_chat_rooms "syncs chat-rooms"/);
    expect(dsl).toMatch(/-> extension\.mesh_doc_chat_presence "syncs chat-presence"/);
  });

  test("captures the access option and labels the node with it", () => {
    const signals = analysis.meshOrPeerSignals ?? [];
    // chat-rooms declares an access option; chat-presence does not.
    const rooms = signals.find((s) => s.key === "chat-rooms");
    expect(rooms?.access).toEqual({
      read: "() => true",
      write: "(identity) => identity !== undefined",
    });
    expect(signals.find((s) => s.key === "chat-presence")?.access).toBeUndefined();

    // The read predicate reaches the chat-rooms node's label.
    const dsl = generateStructurizrDSL(analysis);
    expect(dsl).toMatch(/mesh_doc_chat_rooms = container[^\n]*access read=\(\) => true/);
  });

  test("emits the mesh transport stack as a dependency chain", () => {
    const dsl = generateStructurizrDSL(analysis);
    // The four transport nodes.
    expect(dsl).toContain('mesh_net_adapter = container "MeshNetworkAdapter"');
    expect(dsl).toContain('mesh_webrtc_adapter = container "MeshWebRTCAdapter"');
    expect(dsl).toContain('mesh_signaling_client = container "MeshSignalingClient"');
    expect(dsl).toContain('mesh_signaling_endpoint = container "Signalling endpoint"');
    // Chained, not a single arrow.
    expect(dsl).toContain('extension.mesh_net_adapter -> extension.mesh_webrtc_adapter "wraps"');
    expect(dsl).toContain(
      'extension.mesh_webrtc_adapter -> extension.mesh_signaling_client "negotiates via"'
    );
    expect(dsl).toContain(
      'extension.mesh_signaling_client -> extension.mesh_signaling_endpoint "connects to"'
    );
    // Each mesh document routes through the transport head.
    expect(dsl).toMatch(
      /extension\.mesh_doc_chat_rooms -> extension\.mesh_net_adapter "syncs through"/
    );
    // No $peerState in this fixture — no relay hop.
    expect(dsl).not.toContain("peer_relay");
  });

  test("a project with no mesh state emits no mesh containers", () => {
    const meshFree: ArchitectureAnalysis = {
      projectRoot: "/x",
      system: { name: "X", version: "1.0.0" },
      contexts: {
        background: {
          type: "background",
          entryPoint: "background.ts",
          handlers: [],
          chromeAPIs: [],
          externalAPIs: [],
          dependencies: [],
        },
      },
      messageFlows: [],
      integrations: [],
    };
    // The element style is always declared; what must be absent is any
    // mesh-document container (its `mesh_doc_` identifier prefix).
    expect(generateStructurizrDSL(meshFree)).not.toContain("mesh_doc_");
  });
});
