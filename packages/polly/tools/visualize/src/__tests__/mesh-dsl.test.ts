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
