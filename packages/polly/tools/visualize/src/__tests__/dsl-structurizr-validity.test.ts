// DSL that Structurizr rejects, found by generating every example:
//   - full-featured: GET_SETTINGS matched both the query list ("get") and the
//     command list ("set"), so its component was declared in two groups.
//   - webrtc-p2p-chat: two call sites (or two handlers in one context) gave
//     the same `client -> server "Sends offer"` relationship twice.
//   - todo-list: a flow sent from a BDD step file had context `unknown`, and
//     `extension.unknown` is no element.
//   - dynamic view keys such as "General Flow": Structurizr allows only
//     [A-Za-z0-9_-] in a view key, and keys must be unique.

import { describe, expect, test } from "bun:test";
import type {
  ArchitectureAnalysis,
  ContextInfo,
  MessageFlow,
} from "../../../analysis/src/types/architecture";
import type { MessageHandler } from "../../../analysis/src/types/core";
import { claimViewKey, generateStructurizrDSL } from "../codegen/structurizr";

function handler(node: string, messageType: string, line = 1): MessageHandler {
  return {
    node,
    messageType,
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: `src/${node}/handlers.ts`, line },
  };
}

function context(type: string, handlers: MessageHandler[]): ContextInfo {
  return {
    type,
    entryPoint: `src/${type}/index.ts`,
    handlers,
    chromeAPIs: [],
    externalAPIs: [],
    dependencies: [],
  };
}

function flow(messageType: string, from: string, to: string[], line = 1): MessageFlow {
  return {
    messageType,
    from,
    to,
    sequence: [
      {
        step: 1,
        action: `${from}.send(${messageType})`,
        context: from,
        location: { file: `src/${from}/x.ts`, line },
      },
    ],
  };
}

function analysisOf(
  contexts: Record<string, ContextInfo>,
  messageFlows: MessageFlow[] = []
): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "Test", version: "1.0.0" },
    contexts,
    messageFlows,
    integrations: [],
  };
}

function generate(analysis: ArchitectureAnalysis): string {
  return generateStructurizrDSL(analysis, {
    includeDynamicDiagrams: true,
    includeComponentDiagrams: true,
    componentDiagramContexts: Object.keys(analysis.contexts),
  });
}

function count(haystack: string, needle: string): number {
  return haystack.split(needle).length - 1;
}

describe("claimViewKey", () => {
  test("replaces each run of disallowed characters with one underscore", () => {
    expect(claimViewKey("General Flow", new Set())).toBe("General_Flow");
    expect(claimViewKey("Auth / Session  Flow!", new Set())).toBe("Auth_Session_Flow");
    expect(claimViewKey("Components_Background", new Set())).toBe("Components_Background");
    expect(claimViewKey("kebab-case-key", new Set())).toBe("kebab-case-key");
  });

  test("a name with no allowed characters still gets a key", () => {
    expect(claimViewKey("  ?? ", new Set())).toBe("View");
  });

  test("a repeated key gets the first free numeric suffix", () => {
    const used = new Set<string>();
    expect(claimViewKey("Authentication Flow", used)).toBe("Authentication_Flow");
    expect(claimViewKey("Authentication Flow", used)).toBe("Authentication_Flow_2");
    expect(claimViewKey("Authentication_Flow", used)).toBe("Authentication_Flow_3");
    expect([...used]).toEqual([
      "Authentication_Flow",
      "Authentication_Flow_2",
      "Authentication_Flow_3",
    ]);
  });

  test("every key emitted matches Structurizr's allowed form", () => {
    const used = new Set<string>();
    for (const name of ["a b", "a b", "ü-ñ", "x.y", "", "1 2 3"]) {
      expect(claimViewKey(name, used)).toMatch(/^[A-Za-z0-9_-]+$/);
    }
    expect(used.size).toBe(6);
  });
});

describe("component groups", () => {
  test("a type matching both the query and command lists is declared once", () => {
    // GET_SETTINGS contains "get" and "set". SETTINGS_UPDATE and GET_BOOKMARKS
    // make both lists long enough (two each) to become groups.
    const dsl = generate(
      analysisOf({
        background: context("background", [
          handler("background", "TAB_GET_CURRENT", 1),
          handler("background", "SETTINGS_UPDATE", 2),
          handler("background", "GET_SETTINGS", 3),
          handler("background", "GET_BOOKMARKS", 4),
        ]),
      })
    );
    expect(count(dsl, "get_settings_handler = component")).toBe(1);
    expect(count(dsl, "settings_update_handler = component")).toBe(1);
  });
});

describe("message flow relationships", () => {
  const contexts = {
    client: context("client", [handler("client", "offer")]),
    server: context("server", [handler("server", "offer"), handler("server", "join")]),
  };

  test("two flows with the same ends and label are one relationship", () => {
    const dsl = generate(
      analysisOf(contexts, [
        flow("offer", "client", ["server"], 10),
        flow("offer", "client", ["server"], 20),
        flow("offer", "client", ["server", "server"], 30),
      ])
    );
    expect(count(dsl, 'extension.client -> extension.server "Sends offer"')).toBe(1);
  });

  test("a dynamic view step is not repeated for a second call site", () => {
    const dsl = generate(
      analysisOf(contexts, [
        flow("offer", "client", ["server"], 10),
        flow("offer", "client", ["server"], 20),
      ])
    );
    expect(count(dsl, 'extension.client -> extension.server "offer"')).toBe(1);
  });

  test("a flow from an unresolved context is omitted, not drawn from a missing element", () => {
    const dsl = generate(
      analysisOf(contexts, [
        flow("join", "unknown", ["server"]),
        flow("join", "popup", ["server"]),
        flow("offer", "client", ["server"]),
      ])
    );
    expect(dsl).not.toContain("extension.unknown");
    expect(dsl).not.toContain("extension.popup");
    expect(dsl).toContain('extension.client -> extension.server "Sends offer"');
  });

  test("a recipient with no container is dropped from the flow", () => {
    const dsl = generate(analysisOf(contexts, [flow("offer", "client", ["server", "worker"])]));
    expect(dsl).not.toContain("extension.worker");
    expect(dsl).toContain('extension.client -> extension.server "Sends offer"');
  });
});

describe("view keys in generated DSL", () => {
  test("dynamic views carry a valid, unique key and the readable title", () => {
    // The message flows give an "Authentication Flow" and a "General Flow";
    // a user-provided diagram keyed "General Flow" collides with the latter.
    const analysis = analysisOf(
      {
        background: context("background", [handler("background", "USER_LOGIN")]),
        popup: context("popup", []),
      },
      [flow("USER_LOGIN", "popup", ["background"]), flow("PING", "popup", ["background"])]
    );
    const dsl = generateStructurizrDSL(analysis, {
      includeDynamicDiagrams: true,
      includeComponentDiagrams: true,
      componentDiagramContexts: ["background", "popup"],
      dynamicDiagrams: [
        {
          key: "General Flow",
          scope: "extension",
          title: "General Flow",
          steps: [{ order: 1, from: "user", to: "extension.popup", description: "Uses" }],
        },
      ],
    });

    const keys = [
      ...dsl.matchAll(
        /^\s+(?:systemContext|container|component|dynamic|deployment)\s+\S+\s+"([^"]*)"/gm
      ),
    ].map((m) => m[1]);
    expect(keys).toEqual([
      "SystemContext",
      "Containers",
      "Components_Background",
      "Components_Popup",
      "General_Flow",
      "Authentication_Flow",
      "General_Flow_2",
    ]);
    expect(count(dsl, 'title "General Flow"')).toBe(2);
    expect(dsl).toContain('title "Authentication Flow"');
  });

  test("generating twice from one generator input gives identical DSL", () => {
    const analysis = analysisOf(
      { background: context("background", []), popup: context("popup", []) },
      [flow("USER_LOGIN", "popup", ["background"])]
    );
    expect(generate(analysis)).toBe(generate(analysis));
  });
});
