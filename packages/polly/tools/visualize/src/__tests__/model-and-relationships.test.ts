import { describe, expect, test } from "bun:test";
import type {
  ArchitectureAnalysis,
  ContextInfo,
  ExternalIntegration,
} from "../../../analysis/src/types/architecture";
import type { MeshOrPeerSignalInfo, MessageHandler } from "../../../analysis/src/types/core";
import { generateStructurizrDSL, type StructurizrDSLOptions } from "../codegen/structurizr";
import type { OverlaySnapshot } from "../mesh-snapshot";

// The model-section generators (workspace header, external systems, the main
// system and its containers, mesh documents and transport, the snapshot
// overlay's peers, and the container/component relationships) are private, so
// these tests read them through the DSL `generateStructurizrDSL` emits.

function context(type: string, overrides: Partial<ContextInfo> = {}): ContextInfo {
  return {
    type,
    entryPoint: `${type}.ts`,
    handlers: [],
    chromeAPIs: [],
    externalAPIs: [],
    dependencies: [],
    ...overrides,
  };
}

function handler(messageType: string, overrides: Partial<MessageHandler> = {}): MessageHandler {
  return {
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: "/test/background.ts", line: 1 },
    messageType,
    ...overrides,
  };
}

function analysis(overrides: Partial<ArchitectureAnalysis> = {}): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "Test Extension", version: "1.0.0", description: "Test" },
    contexts: {},
    messageFlows: [],
    integrations: [],
    ...overrides,
  };
}

function signal(
  kind: "mesh" | "peer",
  key: string,
  overrides: Partial<MeshOrPeerSignalInfo> = {}
): MeshOrPeerSignalInfo {
  return { kind, key, variableName: "s", filePath: "/test/src/a.ts", line: 1, ...overrides };
}

function call(endpoint: string, method = "GET") {
  return { method, endpoint, location: { file: "/test/a.ts", line: 1 } };
}

function integration(overrides: Partial<ExternalIntegration>): ExternalIntegration {
  return { type: "api", name: "Api", usedIn: [], ...overrides };
}

const dslOf = (a: ArchitectureAnalysis, options?: StructurizrDSLOptions) =>
  generateStructurizrDSL(a, options);

/** The `model { ... }` section, exactly as generated. */
function modelOf(dsl: string): string {
  const start = dsl.indexOf("  model {");
  const end = dsl.indexOf("\n\n  views {");
  return dsl.slice(start, end);
}

/** Lines matching `pattern`, in output order. */
function linesMatching(dsl: string, pattern: RegExp): string[] {
  return dsl.split("\n").filter((line) => pattern.test(line));
}

describe("workspace header", () => {
  test("escapes name and description and declares hierarchical identifiers", () => {
    const dsl = dslOf(
      analysis({ system: { name: 'My "Ext"', version: "1", description: 'Does "x"' } })
    );
    expect(
      dsl.startsWith(
        'workspace "My \\"Ext\\"" "Does \\"x\\"" {\n\n  !identifiers hierarchical\n\n  model {'
      )
    ).toBe(true);
  });

  test("an absent description renders as an empty string", () => {
    const dsl = dslOf(analysis({ system: { name: "N", version: "1" } }));
    expect(dsl.startsWith('workspace "N" "" {\n\n  !identifiers hierarchical\n\n  model {')).toBe(
      true
    );
  });

  test("ADRs add an !adrs directive with their directory", () => {
    const adr = {
      id: "1",
      title: "t",
      status: "accepted" as const,
      date: "2026-01-01",
      context: "c",
      decision: "d",
      consequences: "q",
      source: "docs/adr/1.md",
    };
    const dsl = dslOf(analysis({ adrs: { adrs: [adr], directory: "docs/adr" } }));
    expect(
      dsl.startsWith(
        'workspace "Test Extension" "Test" {\n\n  !identifiers hierarchical\n  !adrs docs/adr\n\n  model {'
      )
    ).toBe(true);
  });

  test("an empty ADR collection adds no directive", () => {
    const dsl = dslOf(analysis({ adrs: { adrs: [], directory: "docs/adr" } }));
    expect(dsl).not.toContain("!adrs");
  });
});

describe("model section", () => {
  test("an empty analysis renders the person, the system, and nothing else", () => {
    expect(modelOf(dslOf(analysis()))).toBe(
      [
        "  model {",
        '    user = person "User" "Extension user"',
        "",
        '    extension = softwareSystem "Test Extension" {\n\n\n\n    }',
        "  }",
      ].join("\n\n")
    );
  });

  test("a single context renders as a container between the system braces", () => {
    const model = modelOf(dslOf(analysis({ contexts: { popup: context("popup") } })));
    expect(model).toBe(
      [
        "  model {",
        '    user = person "User" "Extension user"',
        "",
        [
          '    extension = softwareSystem "Test Extension" {',
          '      popup = container "Popup" "Popup context" "Browser Action Popup" {\n      }',
          '      user -> extension.popup "Uses"',
          "    }",
        ].join("\n\n"),
        "  }",
      ].join("\n\n")
    );
  });

  test("the system name is escaped", () => {
    const dsl = dslOf(analysis({ system: { name: 'A "B"', version: "1" } }));
    expect(dsl).toContain('    extension = softwareSystem "A \\"B\\"" {');
  });

  test("deployment nodes add a deployment environment inside the model", () => {
    const model = modelOf(
      dslOf(analysis(), {
        deploymentNodes: [{ name: "Browser", technology: "Chrome", containerInstances: [] }],
      })
    );
    expect(model).toContain('    deploymentEnvironment "Production" {');
    expect(model.endsWith("\n\n  }")).toBe(true);
  });

  test("no deployment nodes, no deployment environment", () => {
    expect(dslOf(analysis())).not.toContain("deploymentEnvironment");
  });
});

describe("external systems", () => {
  test("an api integration with a description renders as a REST API system", () => {
    const dsl = dslOf(
      analysis({ integrations: [integration({ name: "Todo API", description: 'The "todo" API' })] })
    );
    expect(dsl).toContain(
      [
        '    todo_api = softwareSystem "Todo API" "The \\"todo\\" API" {',
        '      tags "External System" "REST API"',
        "    }",
      ].join("\n")
    );
  });

  test("a websocket integration is tagged WebSocket", () => {
    const dsl = dslOf(
      analysis({
        integrations: [integration({ type: "websocket", name: "Live", description: "d" })],
      })
    );
    expect(dsl).toContain(
      [
        '    live = softwareSystem "Live" "d" {',
        '      tags "External System" "WebSocket"',
        "    }",
      ].join("\n")
    );
  });

  test("with no description, the first three endpoints and the distinct methods describe it", () => {
    const dsl = dslOf(
      analysis({
        integrations: [
          integration({
            name: 'Svc "1"',
            calls: [call("/a", "GET"), call("/b", "POST"), call("/c", "GET"), call("/d", "PUT")],
          }),
        ],
      })
    );
    expect(dsl).toContain(
      '    svc_1 = softwareSystem "Svc \\"1\\"" "External API with endpoints: /a, /b, /c. Methods: GET, POST, PUT" {'
    );
  });

  test("an explicit description wins over the call-derived one", () => {
    const dsl = dslOf(
      analysis({ integrations: [integration({ description: "given", calls: [call("/a")] })] })
    );
    expect(dsl).toContain('    api = softwareSystem "Api" "given" {');
  });

  test("no description and no calls leaves an empty description", () => {
    const dsl = dslOf(analysis({ integrations: [integration({ calls: [] })] }));
    expect(dsl).toContain('    api = softwareSystem "Api" "" {');
    const dsl2 = dslOf(analysis({ integrations: [integration({})] }));
    expect(dsl2).toContain('    api = softwareSystem "Api" "" {');
  });

  test("non-network integrations are not rendered", () => {
    const dsl = dslOf(
      analysis({
        integrations: [
          integration({ type: "storage", name: "Store" }),
          integration({ type: "browser-api", name: "Tabs" }),
          integration({ type: "external-script", name: "Script" }),
        ],
      })
    );
    expect(dsl).not.toContain('softwareSystem "Store"');
    expect(dsl).not.toContain('softwareSystem "Tabs"');
    expect(dsl).not.toContain('softwareSystem "Script"');
    expect(modelOf(dsl)).toBe(modelOf(dslOf(analysis())));
  });

  test("two systems are joined line by line", () => {
    const model = modelOf(
      dslOf(
        analysis({
          integrations: [
            integration({ name: "A", description: "a" }),
            integration({ name: "B", description: "b" }),
          ],
        })
      )
    );
    expect(model).toContain(
      [
        '    a = softwareSystem "A" "a" {',
        '      tags "External System" "REST API"',
        "    }",
        '    b = softwareSystem "B" "b" {',
      ].join("\n")
    );
  });
});

describe("external API relationships", () => {
  test("a context calling an integration endpoint gets a Calls edge", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", { externalAPIs: [call("/todos")] }),
          content: context("content", { externalAPIs: [call("/other")] }),
        },
        integrations: [integration({ name: "Todo API", calls: [call("/todos")] })],
      })
    );
    expect(linesMatching(dsl, /-> todo_api/)).toEqual([
      '      extension.background -> todo_api "Calls"',
    ]);
  });

  test("a websocket integration gets a Connects to edge", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background", { externalAPIs: [call("wss://x")] }) },
        integrations: [integration({ type: "websocket", name: "Live", calls: [call("wss://x")] })],
      })
    );
    expect(linesMatching(dsl, /-> live/)).toEqual([
      '      extension.background -> live "Connects to"',
    ]);
  });

  test("a non-network integration with a matching endpoint gets no edge", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background", { externalAPIs: [call("/s")] }) },
        integrations: [integration({ type: "storage", name: "Store", calls: [call("/s")] })],
      })
    );
    expect(linesMatching(dsl, /-> store/)).toEqual([]);
  });

  test("an integration without calls is never used", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background", { externalAPIs: [call("/s")] }) },
        integrations: [integration({ name: "Bare", description: "d" })],
      })
    );
    expect(linesMatching(dsl, /-> bare/)).toEqual([]);
  });

  test("every context that calls the integration gets its own edge", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", { externalAPIs: [call("/x")] }),
          popup: context("popup", { externalAPIs: [call("/y"), call("/x")] }),
        },
        integrations: [integration({ name: "X", calls: [call("/z"), call("/x")] })],
      })
    );
    expect(linesMatching(dsl, /-> x "/)).toEqual([
      '      extension.background -> x "Calls"',
      '      extension.popup -> x "Calls"',
    ]);
  });
});

describe("containers", () => {
  test("technology comes from the context type; unknown types are Application Context", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          content: context("content"),
          worker: context("worker", { description: 'Runs "jobs"' }),
        },
      })
    );
    expect(dsl).toContain(
      '      content = container "Content" "Content context" "Content Script" {\n      }'
    );
    expect(dsl).toContain(
      '      worker = container "Worker" "Runs \\"jobs\\"" "Application Context" {\n      }'
    );
  });

  test("a component-diagram context with nothing in it still opens its component block", () => {
    const dsl = dslOf(analysis({ contexts: { background: context("background") } }));
    expect(dsl).toContain(
      '      background = container "Background" "Background context" "Service Worker / Background Script" {\n\n\n\n      }'
    );
  });

  test("component diagrams can be switched off", () => {
    const dsl = dslOf(
      analysis({ contexts: { background: context("background", { chromeAPIs: ["tabs"] }) } }),
      { includeComponentDiagrams: false }
    );
    expect(dsl).toContain(
      '      background = container "Background" "Background context" "Service Worker / Background Script" {\n      }'
    );
    expect(dsl).not.toContain("chrome_tabs");
  });

  test("only contexts listed in componentDiagramContexts get components", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", { chromeAPIs: ["tabs"] }),
          popup: context("popup", { chromeAPIs: ["storage"] }),
        },
      }),
      { componentDiagramContexts: ["popup"] }
    );
    expect(dsl).toContain("chrome_storage = component");
    expect(dsl).not.toContain("chrome_tabs");
    expect(dsl).toContain(
      '      background = container "Background" "Background context" "Service Worker / Background Script" {\n      }'
    );
  });
});

describe("components", () => {
  test("UI components render with their description, or a default", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          popup: context("popup", {
            components: [
              {
                name: "TodoList",
                type: "function",
                filePath: "a.tsx",
                line: 1,
                description: 'Shows "todos"',
              },
              { name: "Header", type: "function", filePath: "a.tsx", line: 2 },
            ],
          }),
        },
      }),
      { componentDiagramContexts: ["popup"] }
    );
    expect(dsl).toContain(
      [
        '      popup = container "Popup" "Popup context" "Browser Action Popup" {',
        '        todolist = component "TodoList" "Shows \\"todos\\"" {',
        '          tags "UI Component"',
        "        }",
        '        header = component "Header" "UI component" {',
        '          tags "UI Component"',
        "        }",
        "",
        "",
        "      }",
      ].join("\n")
    );
  });

  test("Chrome APIs render as external components", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background", { chromeAPIs: ["storage", "tabs"] }) },
      })
    );
    expect(dsl).toContain(
      [
        '      background = container "Background" "Background context" "Service Worker / Background Script" {',
        '        chrome_storage = component "Chrome Storage API" "Browser API for storage" {',
        '          tags "Chrome API" "External"',
        "        }",
        '        chrome_tabs = component "Chrome Tabs API" "Browser API for tabs" {',
        '          tags "Chrome API" "External"',
        "        }",
        "",
        "",
        "      }",
      ].join("\n")
    );
  });

  test("a REST handler keeps its raw name and is tagged REST Endpoint", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          server: context("server", {
            handlers: [
              handler("POST /items", { handlerKind: "rest" }),
              handler("POST /items", { location: { file: "/test/other.ts", line: 9 } }),
            ],
          }),
        },
      }),
      { componentDiagramContexts: ["server"] }
    );
    const defs = linesMatching(dsl, / = component /);
    expect(defs).toEqual([
      '        post_items = component "POST /items" "Processes POST /items messages and coordinates business logic" {',
    ]);
    expect(dsl).toContain('          tags "Message Handler" "REST Endpoint"');
    // The first handler of the type supplies the properties.
    expect(dsl).toContain('            "Source" "background.ts:1"');
    expect(dsl).not.toContain("other.ts:9");
  });

  test("a non-REST handler gets the Handler component name and no REST tag", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", {
            handlers: [handler("PING_PONG"), handler("PING_PONG", { handlerKind: "rest" })],
          }),
        },
      })
    );
    expect(linesMatching(dsl, / = component /)).toEqual([
      '        ping_pong_handler = component "Ping Pong Handler" "Processes PING_PONG messages and coordinates business logic" {',
    ]);
    expect(dsl).toContain('          tags "Message Handler"\n');
    expect(dsl).not.toContain("REST Endpoint");
  });

  test("handlers of distinct types each become a component, in first-seen order", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", {
            handlers: [handler("ALPHA"), handler("BETA"), handler("ALPHA")],
          }),
        },
      })
    );
    expect(linesMatching(dsl, / = component /).map((l) => l.trim().split(" ")[0])).toEqual([
      "alpha_handler",
      "beta_handler",
    ]);
  });
});

describe("Chrome API relationships", () => {
  function chromeEdges(api: string, types: string[]): string[] {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", {
            chromeAPIs: [api],
            handlers: types.map((t) => handler(t)),
          }),
        },
      })
    );
    return linesMatching(dsl, / -> chrome_/);
  }

  test("storage reads for get/load handlers and writes for the rest", () => {
    expect(chromeEdges("storage", ["GET_TODOS", "LOAD_ALL", "SAVE"])).toEqual([
      '        get_todos_handler -> chrome_storage "Reads from storage"',
      '        load_all_handler -> chrome_storage "Reads from storage"',
      '        save_handler -> chrome_storage "Writes to storage"',
    ]);
  });

  test("tabs, runtime, and any other API get their own descriptions", () => {
    expect(chromeEdges("tabs", ["GET_X"])).toEqual([
      '        get_x_handler -> chrome_tabs "Manages browser tabs"',
    ]);
    expect(chromeEdges("runtime", ["GET_X"])).toEqual([
      '        get_x_handler -> chrome_runtime "Sends messages"',
    ]);
    expect(chromeEdges("alarms", ["GET_X"])).toEqual([
      '        get_x_handler -> chrome_alarms "Uses alarms"',
    ]);
  });

  test("every API is linked from every handler type, API-major", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", {
            chromeAPIs: ["tabs", "runtime"],
            handlers: [handler("A"), handler("B"), handler("A")],
          }),
        },
      })
    );
    expect(linesMatching(dsl, / -> chrome_/)).toEqual([
      '        a_handler -> chrome_tabs "Manages browser tabs"',
      '        b_handler -> chrome_tabs "Manages browser tabs"',
      '        a_handler -> chrome_runtime "Sends messages"',
      '        b_handler -> chrome_runtime "Sends messages"',
    ]);
  });

  test("a REST handler is linked by its raw-name identifier", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          server: context("server", {
            chromeAPIs: ["alarms"],
            handlers: [handler("GET /x", { handlerKind: "rest" })],
          }),
        },
      }),
      { componentDiagramContexts: ["server"] }
    );
    expect(linesMatching(dsl, / -> chrome_/)).toEqual([
      '        get_x -> chrome_alarms "Uses alarms"',
    ]);
  });
});

describe("user-provided relationships", () => {
  test("render inside each component-diagram context, with technology and tags", () => {
    const dsl = dslOf(analysis({ contexts: { background: context("background") } }), {
      relationships: [
        {
          from: "Foo Handler",
          to: "Bar Service",
          description: 'calls "bar"',
          technology: 'RPC "v2"',
          tags: ["Sync", "Critical"],
        },
        { from: "a", to: "b", description: "plain" },
        { from: "c", to: "d", description: "untagged", tags: [] },
      ],
    });
    expect(dsl).toContain(
      [
        '      background = container "Background" "Background context" "Service Worker / Background Script" {',
        "",
        "",
        '        foo_handler -> bar_service "calls \\"bar\\"" "RPC \\"v2\\"" {',
        '          tags "Sync" "Critical"',
        "        }",
        '        a -> b "plain" {',
        "        }",
        '        c -> d "untagged" {',
        "        }",
        "      }",
      ].join("\n")
    );
  });
});

describe("user relationships", () => {
  test("only the UI contexts are used by the user, in context order", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          devtools: context("devtools"),
          background: context("background"),
          options: context("options"),
          content: context("content"),
          popup: context("popup"),
        },
      })
    );
    expect(linesMatching(dsl, /^ {6}user -> /)).toEqual([
      '      user -> extension.devtools "Uses"',
      '      user -> extension.options "Uses"',
      '      user -> extension.popup "Uses"',
    ]);
  });
});

describe("mesh documents", () => {
  test("mesh and peer documents render as tagged containers, deduplicated by key", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background") },
        meshOrPeerSignals: [
          signal("mesh", "chat-rooms"),
          signal("mesh", "chat-rooms", { filePath: "/test/src/b.ts" }),
          signal("peer", "presence"),
        ],
      })
    );
    expect(dsl).toContain(
      [
        `      mesh_doc_chat_rooms = container "chat-rooms" "Mesh Document — deriveDocumentId('chat-rooms')" "$meshState" {`,
        '        tags "Mesh Document"',
        "      }",
        `      mesh_doc_presence = container "presence" "Peer Document — deriveDocumentId('presence')" "$peerState" {`,
        '        tags "Peer Document"',
        "      }",
      ].join("\n")
    );
    expect(linesMatching(dsl, /mesh_doc_chat_rooms = container/)).toHaveLength(1);
  });

  test("keys are escaped in the name and the description", () => {
    const dsl = dslOf(analysis({ meshOrPeerSignals: [signal("mesh", 'a"b')] }));
    expect(dsl).toContain(
      `      mesh_doc_a_b = container "a\\"b" "Mesh Document — deriveDocumentId('a\\"b')" "$meshState" {`
    );
  });

  test("access predicates are shown, clipped past 32 characters", () => {
    const exactly32 = "x".repeat(32);
    const over = `${"y".repeat(32)}z`;
    const dsl = dslOf(
      analysis({
        meshOrPeerSignals: [signal("mesh", "doc", { access: { read: exactly32, write: over } })],
      })
    );
    expect(dsl).toContain(
      `      mesh_doc_doc = container "doc" "Mesh Document — deriveDocumentId('doc') · access read=${exactly32} write=${"y".repeat(31)}…" "$meshState" {`
    );
  });

  test("no signals leaves no mesh documents or transport", () => {
    const dsl = dslOf(analysis({ meshOrPeerSignals: [] }));
    expect(dsl).not.toContain("mesh_doc_");
    expect(dsl).not.toContain('tags "Mesh Transport"');
    expect(modelOf(dsl)).toBe(modelOf(dslOf(analysis())));
  });
});

describe("context for a mesh document's file", () => {
  function syncEdges(contexts: Record<string, ContextInfo>, filePath: string): string[] {
    const dsl = dslOf(
      analysis({ contexts, meshOrPeerSignals: [signal("mesh", "doc", { filePath })] })
    );
    return linesMatching(dsl, / "syncs doc"$/);
  }

  test("a single context owns every file", () => {
    expect(syncEdges({ popup: context("popup", { entryPoint: "" }) }, "/elsewhere/x.ts")).toEqual([
      '      extension.popup -> extension.mesh_doc_doc "syncs doc"',
    ]);
  });

  test("with several contexts, the one whose entry directory contains the file wins", () => {
    const contexts = {
      background: context("background", { entryPoint: "/test/src/background/index.ts" }),
      popup: context("popup", { entryPoint: "/test/src/popup/index.tsx" }),
    };
    expect(syncEdges(contexts, "/test/src/popup/state.ts")).toEqual([
      '      extension.popup -> extension.mesh_doc_doc "syncs doc"',
    ]);
    expect(syncEdges(contexts, "/test/src/background/deep/state.ts")).toEqual([
      '      extension.background -> extension.mesh_doc_doc "syncs doc"',
    ]);
  });

  test("the directory boundary is the last slash, not a prefix of the name", () => {
    const contexts = {
      background: context("background", { entryPoint: "/test/src/background/index.ts" }),
      popup: context("popup", { entryPoint: "/test/src/popup/index.tsx" }),
    };
    expect(syncEdges(contexts, "/test/src/popupx/state.ts")).toEqual([]);
  });

  test("the most specific entry directory wins regardless of order", () => {
    const outerFirst = {
      background: context("background", { entryPoint: "/test/src/index.ts" }),
      popup: context("popup", { entryPoint: "/test/src/popup/index.tsx" }),
    };
    const innerFirst = {
      popup: context("popup", { entryPoint: "/test/src/popup/index.tsx" }),
      background: context("background", { entryPoint: "/test/src/index.ts" }),
    };
    for (const contexts of [outerFirst, innerFirst]) {
      expect(syncEdges(contexts, "/test/src/popup/x.ts")).toEqual([
        '      extension.popup -> extension.mesh_doc_doc "syncs doc"',
      ]);
    }
    expect(syncEdges(outerFirst, "/test/src/other.ts")).toEqual([
      '      extension.background -> extension.mesh_doc_doc "syncs doc"',
    ]);
  });

  test("on an equally specific tie, the first context wins", () => {
    const contexts = {
      background: context("background", { entryPoint: "/test/src/background.ts" }),
      popup: context("popup", { entryPoint: "/test/src/popup.ts" }),
    };
    expect(syncEdges(contexts, "/test/src/state.ts")).toEqual([
      '      extension.background -> extension.mesh_doc_doc "syncs doc"',
    ]);
  });

  test("entry points with no directory, or none at all, never match", () => {
    const contexts = {
      background: context("background", { entryPoint: "background.ts" }),
      popup: context("popup", { entryPoint: "" }),
    };
    expect(syncEdges(contexts, "/test/src/state.ts")).toEqual([]);
  });

  test("an unmatched document is still a node", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          a: context("a", { entryPoint: "/x/a.ts" }),
          b: context("b", { entryPoint: "/y/b.ts" }),
        },
        meshOrPeerSignals: [signal("mesh", "doc", { filePath: "/z/c.ts" })],
      })
    );
    expect(dsl).toContain("mesh_doc_doc = container");
    expect(dsl).not.toContain("syncs doc");
  });
});

describe("mesh transport", () => {
  const MESH_NODES = [
    '      mesh_net_adapter = container "MeshNetworkAdapter" "Signs and encrypts every mesh operation" "Mesh Transport" {',
    '        tags "Mesh Transport"',
    "      }",
    '      mesh_webrtc_adapter = container "MeshWebRTCAdapter" "Peer-to-peer WebRTC data channels" "Mesh Transport" {',
    '        tags "Mesh Transport"',
    "      }",
    '      mesh_signaling_client = container "MeshSignalingClient" "WebRTC offer/answer signalling" "Mesh Transport" {',
    '        tags "Mesh Transport"',
    "      }",
    '      mesh_signaling_endpoint = container "Signalling endpoint" "The rendezvous server peers exchange WebRTC offers through" "Mesh Transport" {',
    '        tags "Mesh Transport"',
    "      }",
  ];
  const PEER_NODE = [
    '      peer_relay = container "Peer relay" "The always-on relay $peerState syncs through" "Peer Transport" {',
    '        tags "Mesh Transport"',
    "      }",
  ];
  const CHAIN = [
    '      extension.mesh_net_adapter -> extension.mesh_webrtc_adapter "wraps"',
    '      extension.mesh_webrtc_adapter -> extension.mesh_signaling_client "negotiates via"',
    '      extension.mesh_signaling_client -> extension.mesh_signaling_endpoint "connects to"',
  ];

  test("mesh documents bring the four-node chain, routed through the network adapter", () => {
    const dsl = dslOf(
      analysis({
        meshOrPeerSignals: [signal("mesh", "a"), signal("mesh", "a"), signal("mesh", "b")],
      })
    );
    expect(dsl).toContain(["      }", "", ...MESH_NODES, "", ...CHAIN, ""].join("\n"));
    expect(dsl).not.toContain("peer_relay");
    expect(linesMatching(dsl, /syncs through"$/)).toEqual([
      '      extension.mesh_doc_a -> extension.mesh_net_adapter "syncs through"',
      '      extension.mesh_doc_b -> extension.mesh_net_adapter "syncs through"',
    ]);
  });

  test("peer documents bring only the relay", () => {
    const dsl = dslOf(analysis({ meshOrPeerSignals: [signal("peer", "p")] }));
    expect(dsl).toContain([...PEER_NODE, "", ""].join("\n"));
    expect(dsl).not.toContain("mesh_net_adapter");
    expect(linesMatching(dsl, / -> extension\.(mesh_|peer_relay)/)).toEqual([
      '      extension.mesh_doc_p -> extension.peer_relay "syncs through"',
    ]);
  });

  test("both kinds bring the chain and the relay", () => {
    const dsl = dslOf(analysis({ meshOrPeerSignals: [signal("peer", "p"), signal("mesh", "m")] }));
    expect(dsl).toContain([...MESH_NODES, ...PEER_NODE].join("\n"));
    expect(linesMatching(dsl, / -> extension\.(mesh_|peer_relay)/)).toEqual([
      ...CHAIN,
      '      extension.mesh_doc_p -> extension.peer_relay "syncs through"',
      '      extension.mesh_doc_m -> extension.mesh_net_adapter "syncs through"',
    ]);
  });
});

describe("snapshot overlay: peers and snapshot-only documents", () => {
  function snap(overrides: Partial<OverlaySnapshot> = {}): OverlaySnapshot {
    return { localPeerId: "me", knownPeerIds: [], presentPeerIds: [], peers: [], ...overrides };
  }

  test("each peer is a person; the local one is tagged distinctly", () => {
    const dsl = dslOf(analysis(), {
      snapshot: snap({ localPeerId: 'me "1"', knownPeerIds: ["other"] }),
    });
    expect(modelOf(dsl)).toContain(
      [
        '    user = person "User" "Extension user"',
        "",
        [
          '    peer_me_1 = person "me \\"1\\"" "Local mesh peer (this node)" {',
          '      tags "Local Mesh Peer"',
          "    }",
          '    peer_other = person "other" "Runtime mesh peer" {',
          '      tags "Mesh Peer"',
          "    }",
        ].join("\n"),
        "",
        "",
        "",
        "    extension = softwareSystem",
      ].join("\n")
    );
  });

  test("peer ids that collide as identifiers get numeric suffixes", () => {
    const dsl = dslOf(analysis(), {
      snapshot: snap({ localPeerId: "a-b", knownPeerIds: ["a_b", "a.b"] }),
    });
    expect(linesMatching(dsl, / = person "a/)).toEqual([
      '    peer_a_b = person "a-b" "Local mesh peer (this node)" {',
      '    peer_a_b_2 = person "a_b" "Runtime mesh peer" {',
      '    peer_a_b_3 = person "a.b" "Runtime mesh peer" {',
    ]);
  });

  test("a document only the snapshot knows renders as a snapshot node", () => {
    const dsl = dslOf(analysis(), {
      snapshot: snap({
        peers: [
          {
            peerId: "me",
            slot: {
              handles: { 'Doc"X': { docSynchronizerExists: true, peerDocumentStatus: "has" } },
            },
          },
        ],
      }),
    });
    expect(dsl).toContain(
      [
        '      mesh_doc_doc_x = container "Doc\\"X" "Mesh document seen only in the runtime snapshot — docId Doc\\"X" "snapshot" {',
        '        tags "Snapshot Document"',
        "      }",
      ].join("\n")
    );
  });

  test("without a snapshot document there is no snapshot node", () => {
    const dsl = dslOf(analysis(), { snapshot: snap() });
    expect(dsl).not.toContain('Snapshot Document"\n');
    expect(dsl).not.toContain('"snapshot" {');
  });
});

describe("component relationships from handlers", () => {
  test("Chrome API edges use the first handler of a type to pick the identifier", () => {
    const dsl = dslOf(
      analysis({
        contexts: {
          server: context("server", {
            chromeAPIs: ["alarms"],
            handlers: [handler("GET /x", { handlerKind: "rest" }), handler("GET /x")],
          }),
        },
      }),
      { componentDiagramContexts: ["server"] }
    );
    expect(linesMatching(dsl, / -> chrome_/)).toEqual([
      '        get_x -> chrome_alarms "Uses alarms"',
    ]);
  });

  test("auto-detected handler relationships carry their technology when given", () => {
    const rel = (to: string, technology?: string) => ({
      from: "PING",
      to,
      description: `to ${to}`,
      ...(technology ? { technology } : {}),
      confidence: "high" as const,
      evidence: [],
    });
    const dsl = dslOf(
      analysis({
        contexts: {
          background: context("background", {
            handlers: [handler("PING", { relationships: [rel("db", 'SQL "x"'), rel("cache")] })],
          }),
        },
      })
    );
    expect(dsl).toContain(
      [
        '        ping_handler -> db "to db" "SQL \\"x\\"" {',
        '          tags "Auto-detected"',
        "        }",
        '        ping_handler -> cache "to cache" {',
        '          tags "Auto-detected"',
        "        }",
      ].join("\n")
    );
  });
});

describe("mesh relationships", () => {
  test("one sync edge per context and key, however often the key is declared", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background") },
        meshOrPeerSignals: [
          signal("mesh", "doc"),
          signal("mesh", "doc", { filePath: "/test/src/b.ts" }),
        ],
      })
    );
    expect(linesMatching(dsl, / "syncs doc"$/)).toEqual([
      '      extension.background -> extension.mesh_doc_doc "syncs doc"',
    ]);
  });

  test("a snapshot-only document opens the system body directly", () => {
    const dsl = dslOf(analysis(), {
      snapshot: {
        localPeerId: "me",
        knownPeerIds: [],
        presentPeerIds: [],
        peers: [
          {
            peerId: "me",
            slot: { handles: { D1: { docSynchronizerExists: true, peerDocumentStatus: "has" } } },
          },
        ],
      },
    });
    expect(modelOf(dsl)).toContain(
      '    extension = softwareSystem "Test Extension" {\n\n      mesh_doc_d1 = container "D1"'
    );
  });
});

describe("message flows between modelled contexts", () => {
  test("a flow whose recipients are all unmodelled draws no edge and no flow view", () => {
    const dsl = dslOf(
      analysis({
        contexts: { background: context("background") },
        messageFlows: [
          { messageType: "TODO_ADD", from: "background", to: ["unknown"], sequence: [] },
        ],
      })
    );
    expect(dsl).not.toContain("Sends TODO_ADD");
    expect(dsl).not.toContain("Todo Flow");
  });
});

describe("snapshot overlay edges", () => {
  test("each handle is one sync-tagged edge closing the system body", () => {
    const dsl = dslOf(analysis(), {
      snapshot: {
        localPeerId: "me",
        knownPeerIds: [],
        presentPeerIds: [],
        peers: [
          {
            peerId: "me",
            slot: {
              handles: {
                D1: { docSynchronizerExists: true, peerDocumentStatus: "has" },
                D2: {
                  docSynchronizerExists: true,
                  docSynchronizerKnowsPeer: false,
                  peerDocumentStatus: "wants",
                },
              },
            },
          },
          { peerId: "you", slot: { handles: { D1: { docSynchronizerExists: false } } } },
        ],
      },
    });
    expect(modelOf(dsl)).toContain(
      [
        "      }",
        "",
        '      peer_me -> extension.mesh_doc_d1 "has" {',
        '        tags "sync:has"',
        "      }",
        '      peer_me -> extension.mesh_doc_d2 "wants · peer not added" {',
        '        tags "sync:wants"',
        "      }",
        '      peer_you -> extension.mesh_doc_d1 "unknown · no synchronizer" {',
        '        tags "sync:unknown"',
        "      }",
        "",
        "    }",
      ].join("\n")
    );
  });
});
