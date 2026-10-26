import { describe, expect, test } from "bun:test";
import type { ArchitectureAnalysis, ContextInfo } from "../../../analysis/src/types/architecture";
import type { MeshOrPeerSignalInfo, MessageHandler } from "../../../analysis/src/types/core";
import { claimViewKey, generateStructurizrDSL } from "../codegen/structurizr";

// Generator paths the per-area suites left open: REST handler edges, edges
// to another handler, handlers without relationships among ones with, a
// third colliding message type, view-key trimming, environment-tag spacing,
// and the exact text of the mesh-document and automatic-view sections.

function handler(
  messageType: string,
  to: string[] | undefined,
  extra: Partial<MessageHandler> = {}
): MessageHandler {
  return {
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: "background.ts", line: 1 },
    messageType,
    ...(to
      ? {
          relationships: to.map((target) => ({
            from: `${messageType}_handler`,
            to: target,
            description: `${messageType} to ${target}`,
            confidence: "high" as const,
            evidence: [],
          })),
        }
      : {}),
    ...extra,
  };
}

function context(type: string, handlers: MessageHandler[]): ContextInfo {
  return {
    type,
    entryPoint: `${type}.ts`,
    handlers,
    chromeAPIs: [],
    externalAPIs: [],
    dependencies: [],
  };
}

function analysis(
  contexts: Record<string, ContextInfo>,
  extra: Partial<ArchitectureAnalysis> = {}
): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "T", version: "1.0.0", description: "T" },
    contexts,
    messageFlows: [],
    integrations: [],
    ...extra,
  };
}

/** The `dynamic` blocks, each exactly as emitted. */
function dynamicBlocks(dsl: string): string[] {
  return [...dsl.matchAll(/^ {4}dynamic [^\n]*\{\n(?: {6}[^\n]*\n)* {4}\}/gm)].map((m) => m[0]);
}

describe("claimViewKey", () => {
  test("trims every leading and trailing underscore, not just one", () => {
    expect(claimViewKey("__Flow__", new Set())).toBe("Flow");
    expect(claimViewKey("  Flow  ", new Set())).toBe("Flow");
  });
});

describe("handler component identity", () => {
  test("a third colliding message type gets _3, not _2 again", () => {
    const dsl = generateStructurizrDSL(
      analysis({
        background: context("background", [
          handler("Ping", undefined),
          handler("PING", undefined),
          handler("pinG", undefined),
        ]),
      })
    );
    const ids = [...dsl.matchAll(/^ +(\w+) = component "([^"]+)"/gm)].map((m) => [m[1], m[2]]);
    expect(ids).toEqual([
      ["ping_handler", "Ping Handler"],
      ["ping_handler_2", "Ping Handler 2"],
      ["ping_handler_3", "Ping Handler 3"],
    ]);
  });

  test("a REST handler's edges and flow steps start at its REST id", () => {
    const dsl = generateStructurizrDSL(
      analysis({
        background: context("background", [
          handler("GET /todos", ["db"], { handlerKind: "rest", httpMethod: "GET" }),
        ]),
      })
    );
    expect(dsl).toContain('        get_todos -> db "GET /todos to db" {');
    expect(dsl).toContain(
      '      extension.background.get_todos -> extension.background.db "GET /todos to db"'
    );
  });
});

describe("service components", () => {
  test("an edge to another handler adds no service component for it", () => {
    const dsl = generateStructurizrDSL(
      analysis({
        background: context("background", [
          handler("getA", ["pong_handler", "db"]),
          handler("pong", undefined),
        ]),
      })
    );
    expect([...dsl.matchAll(/^ +(\w+) = component /gm)].map((m) => m[1])).toEqual([
      "geta_handler",
      "pong_handler",
      "db",
    ]);
  });
});

describe("automatic flow views", () => {
  test("handlers without relationships do not count toward the split", () => {
    // 3 handlers with relationships, 1 category: one combined view. Counting
    // the ones without (undefined or empty) would pass 5 and split.
    const dsl = generateStructurizrDSL(
      analysis({
        background: context("background", [
          handler("getA", ["db"]),
          handler("getB", ["db"]),
          handler("getC", ["db"]),
          handler("pz1", undefined),
          handler("pz2", []),
          handler("pz3", []),
          handler("pz4", []),
        ]),
      })
    );
    expect(dynamicBlocks(dsl)).toEqual([
      [
        '    dynamic extension.background "Message_Processing_Flow" "Shows message processing flow through handlers and services" {',
        '      title "Message Processing Flow"',
        '      extension.background.geta_handler -> extension.background.db "getA to db"',
        '      extension.background.getb_handler -> extension.background.db "getB to db"',
        '      extension.background.getc_handler -> extension.background.db "getC to db"',
        "      autoLayout lr",
        "    }",
      ].join("\n"),
    ]);
  });

  test("separate category views follow the component view with nothing between", () => {
    const dsl = generateStructurizrDSL(
      analysis({
        background: context("background", [
          handler("getA", ["db"]),
          handler("addA", ["db"]),
          handler("loginA", ["db"]),
          handler("todoA", ["db"]),
        ]),
      }),
      { includeDefaultStyles: false }
    );
    const views = dsl.slice(dsl.indexOf("\n  views {"), dsl.indexOf("\n    styles {"));
    const view = (key: string, description: string, title: string, from: string) =>
      [
        `    dynamic extension.background "${key}" "${description}" {`,
        `      title "${title}"`,
        `      extension.background.${from.toLowerCase()}_handler -> extension.background.db "${from} to db"`,
        "      autoLayout lr",
        "    }",
      ].join("\n");
    expect(views).toBe(
      `${[
        "\n  views {",
        `    systemContext extension "SystemContext" {\n      include *\n      autoLayout lr\n    }`,
        `    container extension "Containers" {\n      include *\n      autoLayout lr\n    }`,
        `    component extension.background "Components_Background" {\n      include *\n      autoLayout tb\n    }`,
        view(
          "Query_Processing_Flow",
          "Shows read operations flow through query handlers and services",
          "Query Processing Flow",
          "getA"
        ),
        view(
          "Command_Processing_Flow",
          "Shows write operations flow through command handlers and services",
          "Command Processing Flow",
          "addA"
        ),
        view(
          "Authentication_Flow",
          "Shows authentication request processing and service interactions",
          "Authentication Flow",
          "loginA"
        ),
        view(
          "Todo_Management_Flow",
          "Shows todo item operations and service dependencies",
          "Todo Management Flow",
          "todoA"
        ),
      ].join("\n\n")}\n`
    );
  });
});

describe("mesh documents", () => {
  test("the documents section is exactly one container block per key", () => {
    const sig = (key: string, kind: "mesh" | "peer"): MeshOrPeerSignalInfo => ({
      kind,
      key,
      variableName: key,
      filePath: "background.ts",
      line: 1,
    });
    const dsl = generateStructurizrDSL(
      analysis(
        { background: context("background", []) },
        {
          meshOrPeerSignals: [sig("notes", "mesh"), sig("cursor", "peer")],
        }
      )
    );
    const start = dsl.indexOf("      mesh_doc_notes = container");
    const end = dsl.indexOf("\n\n", start);
    expect(dsl.slice(start, end)).toBe(
      [
        `      mesh_doc_notes = container "notes" "Mesh Document — deriveDocumentId('notes')" "$meshState" {`,
        '        tags "Mesh Document"',
        "      }",
        `      mesh_doc_cursor = container "cursor" "Peer Document — deriveDocumentId('cursor')" "$peerState" {`,
        '        tags "Peer Document"',
        "      }",
      ].join("\n")
    );
    // Nothing between the documents and what precedes them but a blank line.
    expect(dsl.slice(0, start).endsWith("\n\n")).toBe(true);
  });
});

describe("deployment environments", () => {
  test("a space after environment: is trimmed", () => {
    const dsl = generateStructurizrDSL(analysis({ background: context("background", []) }), {
      deploymentNodes: [{ name: "Cloud", tags: ["environment: Staging"] }],
    });
    expect(dsl).toContain('    deploymentEnvironment "Staging" {');
    expect(dsl).toContain('    deployment extension "Staging" "Staging" ');
  });
});
