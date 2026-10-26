import { describe, expect, test } from "bun:test";
import type { ADR } from "../../../analysis/src/types/adr";
import type { ArchitectureAnalysis, MessageFlow } from "../../../analysis/src/types/architecture";
import type { MessageHandler } from "../../../analysis/src/types/core";
import { generateStructurizrDSL, type StructurizrDSLOptions } from "../codegen/structurizr";
import type { DeploymentNode, DynamicDiagram } from "../types/structurizr";

// The views, documentation, dynamic-view and deployment generators are
// private, so these tests read them through the DSL `generateStructurizrDSL`
// emits, asserting exact blocks rather than substrings.

function context(type: string, handlers: MessageHandler[] = []) {
  return {
    type,
    entryPoint: `${type}.ts`,
    handlers,
    chromeAPIs: [],
    externalAPIs: [],
    dependencies: [],
  };
}

function analysisWith(
  over: Partial<ArchitectureAnalysis> & { contextTypes?: string[] } = {}
): ArchitectureAnalysis {
  const { contextTypes = ["background"], ...rest } = over;
  const contexts: ArchitectureAnalysis["contexts"] = {};
  for (const type of contextTypes) contexts[type] = context(type);
  return {
    projectRoot: "/test",
    system: { name: "Test Extension", version: "1.0.0", description: "Test" },
    contexts,
    messageFlows: [],
    integrations: [],
    ...rest,
  };
}

function flow(messageType: string, from: string, to: string[]): MessageFlow {
  return { messageType, from, to, sequence: [] };
}

function handler(messageType: string, relationTo: string): MessageHandler {
  return {
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: "background.ts", line: 1 },
    messageType,
    relationships: [
      {
        from: messageType,
        to: relationTo,
        description: `step ${messageType}`,
        technology: "Function Call",
        confidence: "high",
        evidence: [],
      },
    ],
  };
}

function adr(id: string, over: Partial<ADR> = {}): ADR {
  return {
    id,
    title: `Decision ${id}`,
    status: "accepted",
    date: "2026-01-02",
    context: `Context ${id}`,
    decision: "d",
    consequences: "c",
    source: `${id}.md`,
    ...over,
  };
}

/** Options that silence everything optional in the views section. */
const QUIET: StructurizrDSLOptions = {
  includeComponentDiagrams: false,
  includeDynamicDiagrams: false,
  includeDefaultStyles: false,
};

const SYSTEM_CONTEXT = `    systemContext extension "SystemContext" {
      include *
      autoLayout lr
    }`;
const CONTAINERS = `    container extension "Containers" {
      include *
      autoLayout lr
    }`;
const EMPTY_STYLES = "    styles {\n    }";

/** A deployment view: `deployment <scope> <environment> <key> <description>`. */
function deploymentView(env: string): string {
  return [
    `    deployment extension "${env}" "${env.replace(/ /g, "_")}" "${env} environment deployment architecture" {`,
    `      title "${env}"`,
    "      include *",
    "      autoLayout lr",
    "    }",
  ].join("\n");
}

/** Everything from the `views {` line to the end of the workspace. */
function viewsOf(dsl: string): string {
  const start = dsl.indexOf("\n  views {");
  expect(start).toBeGreaterThan(-1);
  return dsl.slice(start + 1);
}

/** The `dynamic` blocks of the DSL, each from `dynamic` to its closing brace. */
function dynamicBlocks(dsl: string): string[] {
  return [...dsl.matchAll(/ {4}dynamic [^\n]*\{\n[\s\S]*?\n {4}\}/g)].map((m) => m[0]);
}

/** The model's deployment environments, from the first to the model's end. */
function deploymentModel(dsl: string): string {
  const start = dsl.indexOf("    deploymentEnvironment ");
  const end = dsl.indexOf("\n\n  }\n\n  views {");
  expect(start).toBeGreaterThan(-1);
  expect(end).toBeGreaterThan(start);
  // The environments are their own model segment, right after the system.
  expect(dsl.slice(start - 8, start)).toBe("\n    }\n\n");
  return dsl.slice(start, end);
}

describe("generateViews", () => {
  test("minimal views section is the two static views and an empty styles block", () => {
    const dsl = generateStructurizrDSL(analysisWith(), QUIET);
    expect(viewsOf(dsl)).toBe(
      ["  views {", SYSTEM_CONTEXT, CONTAINERS, EMPTY_STYLES, "  }", "}"].join("\n\n")
    );
  });

  test("component views follow the configured contexts that exist, in order", () => {
    const dsl = generateStructurizrDSL(analysisWith({ contextTypes: ["background", "popup"] }), {
      ...QUIET,
      includeComponentDiagrams: true,
      componentDiagramContexts: ["popup", "missing", "background"],
    });
    expect(viewsOf(dsl)).toBe(
      [
        "  views {",
        SYSTEM_CONTEXT,
        CONTAINERS,
        `    component extension.popup "Components_Popup" {
      include *
      autoLayout tb
    }`,
        `    component extension.background "Components_Background" {
      include *
      autoLayout tb
    }`,
        EMPTY_STYLES,
        "  }",
        "}",
      ].join("\n\n")
    );
  });

  test("component views default to the background context", () => {
    const dsl = generateStructurizrDSL(analysisWith({ contextTypes: ["background", "popup"] }), {
      includeDynamicDiagrams: false,
      includeDefaultStyles: false,
    });
    expect(dsl).toContain('component extension.background "Components_Background"');
    expect(dsl).not.toContain("component extension.popup");
  });

  test("no component views when the context list is explicitly undefined", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...QUIET,
      includeComponentDiagrams: true,
      componentDiagramContexts: undefined,
    });
    expect(viewsOf(dsl)).toBe(
      ["  views {", SYSTEM_CONTEXT, CONTAINERS, EMPTY_STYLES, "  }", "}"].join("\n\n")
    );
  });

  test("component views are off when includeComponentDiagrams is false", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...QUIET,
      componentDiagramContexts: ["background"],
    });
    expect(dsl).not.toContain("component extension");
  });

  test("dynamic views are on by default and placed after the container view", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [flow("PING", "content", ["background"])],
    });
    const dsl = generateStructurizrDSL(analysis, {
      includeComponentDiagrams: false,
      includeDefaultStyles: false,
    });
    expect(viewsOf(dsl)).toBe(
      [
        "  views {",
        SYSTEM_CONTEXT,
        CONTAINERS,
        `    dynamic extension "General_Flow" "Message flow through the system" {
      title "General Flow"
      extension.content -> extension.background "PING"
      autoLayout lr
    }`,
        EMPTY_STYLES,
        "  }",
        "}",
      ].join("\n\n")
    );
  });

  test("dynamic views are omitted when includeDynamicDiagrams is false", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [flow("PING", "content", ["background"])],
    });
    const dsl = generateStructurizrDSL(analysis, QUIET);
    expect(dsl).not.toContain("dynamic ");
  });

  test("deployment views sit between dynamic views and styles", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...QUIET,
      deploymentNodes: [{ name: "Browser" }],
    });
    expect(viewsOf(dsl)).toBe(
      [
        "  views {",
        SYSTEM_CONTEXT,
        CONTAINERS,
        deploymentView("Production"),
        EMPTY_STYLES,
        "  }",
        "}",
      ].join("\n\n")
    );
  });

  test("an empty deployment node list adds no deployment view or environment", () => {
    const dsl = generateStructurizrDSL(analysisWith(), { ...QUIET, deploymentNodes: [] });
    expect(dsl).not.toContain("deployment");
  });
});

describe("generateDocumentation", () => {
  test("ADRs are imported by !adrs, not emitted as a documentation block", () => {
    // `documentation { decision … }` is not Structurizr DSL; it failed validation.
    const analysis = analysisWith({
      adrs: { directory: "docs/adr", adrs: [adr("0001"), adr("0002")] },
    });
    const dsl = generateStructurizrDSL(analysis, QUIET);
    expect(dsl).toContain("\n  !adrs docs/adr\n");
    expect(dsl).not.toContain("documentation");
    expect(viewsOf(dsl)).toBe(
      ["  views {", SYSTEM_CONTEXT, CONTAINERS, EMPTY_STYLES, "  }", "}"].join("\n\n")
    );
  });

  test("an empty ADR collection emits no documentation section", () => {
    const dsl = generateStructurizrDSL(
      analysisWith({ adrs: { directory: "docs/adr", adrs: [] } }),
      QUIET
    );
    expect(dsl).not.toContain("documentation");
    expect(viewsOf(dsl)).toBe(
      ["  views {", SYSTEM_CONTEXT, CONTAINERS, EMPTY_STYLES, "  }", "}"].join("\n\n")
    );
  });
});

describe("generateDynamicViews", () => {
  const DYN: StructurizrDSLOptions = {
    includeComponentDiagrams: false,
    includeDefaultStyles: false,
  };

  test("flows are grouped by domain in first-seen order, one view per domain", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [
        flow("TODO_ADD", "content", ["background"]),
        flow("USER_LOGIN", "content", ["background"]),
        flow("TODO_REMOVE", "background", ["content"]),
        flow("STATE_SYNC", "content", ["background"]),
        flow("PING", "content", ["background"]),
      ],
    });
    const blocks = dynamicBlocks(generateStructurizrDSL(analysis, DYN));
    expect(blocks).toEqual([
      `    dynamic extension "Todo_Flow" "Todo item creation, updates, and retrieval" {
      title "Todo Flow"
      extension.content -> extension.background "Create item"
      extension.background -> extension.content "Delete item"
      autoLayout lr
    }`,
      `    dynamic extension "Authentication_Flow" "User authentication and session management" {
      title "Authentication Flow"
      extension.content -> extension.background "Authenticate user"
      autoLayout lr
    }`,
      `    dynamic extension "State_Flow" "Application state synchronization" {
      title "State Flow"
      extension.content -> extension.background "STATE_SYNC"
      autoLayout lr
    }`,
      `    dynamic extension "General_Flow" "Message flow through the system" {
      title "General Flow"
      extension.content -> extension.background "PING"
      autoLayout lr
    }`,
    ]);
  });

  test("flows to unknown contexts are dropped before grouping", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [
        flow("PING", "content", ["background", "ghost"]),
        flow("TODO_ADD", "ghost", ["background"]),
      ],
    });
    expect(dynamicBlocks(generateStructurizrDSL(analysis, DYN))).toEqual([
      `    dynamic extension "General_Flow" "Message flow through the system" {
      title "General Flow"
      extension.content -> extension.background "PING"
      autoLayout lr
    }`,
    ]);
  });

  test("a flow to several contexts emits one step per recipient, deduplicated", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content", "offscreen"],
      messageFlows: [
        flow("PING", "background", ["content", "offscreen"]),
        flow("PING", "background", ["content"]),
      ],
    });
    expect(dynamicBlocks(generateStructurizrDSL(analysis, DYN))).toEqual([
      `    dynamic extension "General_Flow" "Message flow through the system" {
      title "General Flow"
      extension.background -> extension.content "PING"
      extension.background -> extension.offscreen "PING"
      autoLayout lr
    }`,
    ]);
  });

  test("message types with quotes are escaped in the step", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [flow('say"hi"', "content", ["background"])],
    });
    expect(dynamicBlocks(generateStructurizrDSL(analysis, DYN))[0]).toContain(
      'extension.content -> extension.background "say\\"hi\\""'
    );
  });

  test("user-provided diagrams come first, then automatic, then flow views", () => {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [flow("PING", "content", ["background"])],
    });
    analysis.contexts["background"] = context("background", [handler("pz", "svc")]);
    const blocks = dynamicBlocks(
      generateStructurizrDSL(analysis, {
        ...DYN,
        // Automatic flow steps name components, so their container needs some.
        includeComponentDiagrams: true,
        dynamicDiagrams: [
          {
            key: "Custom",
            scope: "extension.background",
            title: 'My "Flow"',
            description: 'Does "things"',
            steps: [
              { order: 1, from: "a", to: "b", description: 'Calls "b"' },
              { order: 2, from: "b", to: "c", description: "Calls c" },
            ],
          },
        ],
      })
    );
    expect(blocks).toEqual([
      `    dynamic extension.background "Custom" "Does \\"things\\"" {
      title "My \\"Flow\\""
      a -> b "Calls \\"b\\""
      b -> c "Calls c"
      autoLayout lr
    }`,
      `    dynamic extension.background "Message_Processing_Flow" "Shows message processing flow through handlers and services" {
      title "Message Processing Flow"
      extension.background.pz_handler -> extension.background.svc "step pz"
      autoLayout lr
    }`,
      `    dynamic extension "General_Flow" "Message flow through the system" {
      title "General Flow"
      extension.content -> extension.background "PING"
      autoLayout lr
    }`,
    ]);
  });

  test("a user diagram with empty scope and key and no description falls back", () => {
    const diagram: DynamicDiagram = {
      key: "",
      scope: "",
      title: "Fallback Title",
      steps: [{ order: 1, from: "x", to: "y", description: "go" }],
    };
    const blocks = dynamicBlocks(
      generateStructurizrDSL(analysisWith(), { ...DYN, dynamicDiagrams: [diagram] })
    );
    expect(blocks).toEqual([
      `    dynamic extension "Fallback_Title" "" {
      title "Fallback Title"
      x -> y "go"
      autoLayout lr
    }`,
    ]);
  });

  test("a user diagram is the whole dynamic section when nothing else applies", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...DYN,
      dynamicDiagrams: [
        {
          key: "K",
          scope: "extension",
          title: "T",
          steps: [{ order: 1, from: "a", to: "b", description: "go" }],
        },
      ],
    });
    expect(viewsOf(dsl)).toBe(
      [
        "  views {",
        SYSTEM_CONTEXT,
        CONTAINERS,
        `    dynamic extension "K" "" {
      title "T"
      a -> b "go"
      autoLayout lr
    }`,
        EMPTY_STYLES,
        "  }",
        "}",
      ].join("\n\n")
    );
  });

  test("a user diagram with no steps is still emitted", () => {
    const blocks = dynamicBlocks(
      generateStructurizrDSL(analysisWith(), {
        ...DYN,
        dynamicDiagrams: [{ key: "K", scope: "extension", title: "T", steps: [] }],
      })
    );
    expect(blocks).toEqual([
      `    dynamic extension "K" "" {
      title "T"
      autoLayout lr
    }`,
    ]);
  });

  test("with no diagrams, handlers or flows the dynamic section is empty", () => {
    const dsl = generateStructurizrDSL(analysisWith(), DYN);
    expect(viewsOf(dsl)).toBe(
      ["  views {", SYSTEM_CONTEXT, CONTAINERS, "", EMPTY_STYLES, "  }", "}"].join("\n\n")
    );
  });
});

describe("extractDomainFromMessageType", () => {
  function domainTitle(messageType: string): string | undefined {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [flow(messageType, "content", ["background"])],
    });
    const block = dynamicBlocks(
      generateStructurizrDSL(analysis, { includeComponentDiagrams: false })
    )[0];
    return block?.match(/\n\s*title "([^"]+)"/)?.[1];
  }

  test.each([
    ["USER_PROFILE", "Authentication Flow"],
    ["LOGIN", "Authentication Flow"],
    ["LOGOUT", "Authentication Flow"],
    ["AUTH_CHECK", "Authentication Flow"],
    ["Todo_List", "Todo Flow"],
    ["STATE_PULL", "State Flow"],
    ["PING", "General Flow"],
  ])("%s lands in %s", (messageType, title) => {
    expect(domainTitle(messageType)).toBe(title);
  });

  test("authentication outranks todo and state", () => {
    expect(domainTitle("USER_TODO_STATE")).toBe("Authentication Flow");
  });

  test("todo outranks state", () => {
    expect(domainTitle("TODO_STATE")).toBe("Todo Flow");
  });
});

describe("getMessageDescription", () => {
  function stepLabel(messageType: string): string | undefined {
    const analysis = analysisWith({
      contextTypes: ["background", "content"],
      messageFlows: [flow(messageType, "content", ["background"])],
    });
    const dsl = generateStructurizrDSL(analysis, { includeComponentDiagrams: false });
    return dsl.match(
      / {6}extension\.content -> extension\.background "([^"]*)"\n {6}autoLayout/
    )?.[1];
  }

  test.each([
    ["DO_LOGIN", "Authenticate user"],
    ["DO_LOGOUT", "End session"],
    ["ITEM_ADD", "Create item"],
    ["ITEM_CREATE", "Create item"],
    ["ITEM_REMOVE", "Delete item"],
    ["ITEM_DELETE", "Delete item"],
    ["ITEM_UPDATE", "Update item"],
    ["ITEM_TOGGLE", "Update item"],
    ["ITEM_GET", "Retrieve data"],
    ["ITEM_FETCH", "Retrieve data"],
    ["ITEMS_CLEAR", "Clear items"],
    ["PING", "PING"],
  ])("%s is described as %s", (messageType, label) => {
    expect(stepLabel(messageType)).toBe(label);
  });

  test.each([
    ["LOGIN_LOGOUT", "Authenticate user"],
    ["LOGOUT_ADD", "End session"],
    ["ADD_REMOVE", "Create item"],
    ["REMOVE_UPDATE", "Delete item"],
    ["UPDATE_GET", "Update item"],
    ["GET_CLEAR", "Retrieve data"],
  ])("precedence: %s is %s", (messageType, label) => {
    expect(stepLabel(messageType)).toBe(label);
  });
});

describe("UI flows start with a user action", () => {
  function firstSteps(messageType: string, flows: MessageFlow[]): string[] {
    const analysis = analysisWith({
      contextTypes: ["background", "popup", "options", "devtools", "content"],
      messageFlows: flows,
    });
    const dsl = generateStructurizrDSL(analysis, { includeComponentDiagrams: false });
    const block = dynamicBlocks(dsl).find((b) => b.includes(messageType)) ?? "";
    return block.split("\n").slice(2, -2);
  }

  test.each([
    ["USER_X", "Initiates login"],
    ["TODO_X", "Manages todo items"],
    ["STATE_X", "Requests state"],
    ["PING_X", "Interacts"],
  ])("%s from the popup begins with %s", (messageType, action) => {
    expect(firstSteps(messageType, [flow(messageType, "popup", ["background"])])).toEqual([
      `      user -> extension.popup "${action}"`,
      `      extension.popup -> extension.background "${messageType}"`,
    ]);
  });

  test("the user step targets the first UI flow, not the first flow", () => {
    expect(
      firstSteps("PING_A", [
        flow("PING_A", "content", ["background"]),
        flow("PING_B", "options", ["background"]),
        flow("PING_C", "devtools", ["background"]),
      ])
    ).toEqual([
      '      user -> extension.options "Interacts"',
      '      extension.content -> extension.background "PING_A"',
      '      extension.options -> extension.background "PING_B"',
      '      extension.devtools -> extension.background "PING_C"',
    ]);
  });

  test("devtools counts as a UI context", () => {
    expect(firstSteps("PING_D", [flow("PING_D", "devtools", ["background"])])).toEqual([
      '      user -> extension.devtools "Interacts"',
      '      extension.devtools -> extension.background "PING_D"',
    ]);
  });

  test("non-UI flows have no user step", () => {
    expect(firstSteps("PING_E", [flow("PING_E", "content", ["background"])])).toEqual([
      '      extension.content -> extension.background "PING_E"',
    ]);
  });
});

describe("category titles and descriptions", () => {
  function headers(handlers: MessageHandler[]): string[] {
    const analysis = analysisWith();
    analysis.contexts["background"] = context("background", handlers);
    const dsl = generateStructurizrDSL(analysis);
    return dynamicBlocks(dsl).map((b) => b.split("\n")[0] ?? "");
  }

  test("separate diagrams carry each category's title and description", () => {
    expect(
      headers([
        handler("login", "s"),
        handler("userEdit", "s"),
        handler("todoX", "s"),
        handler("getX", "s"),
        handler("createX", "s"),
        handler("pz", "s"),
      ])
    ).toEqual([
      '    dynamic extension.background "Authentication_Flow" "Shows authentication request processing and service interactions" {',
      '    dynamic extension.background "User_Management_Flow" "Shows user management operations and service dependencies" {',
      '    dynamic extension.background "Todo_Management_Flow" "Shows todo item operations and service dependencies" {',
      '    dynamic extension.background "Query_Processing_Flow" "Shows read operations flow through query handlers and services" {',
      '    dynamic extension.background "Command_Processing_Flow" "Shows write operations flow through command handlers and services" {',
    ]);
  });

  test("the general category has its own title and description", () => {
    expect(
      headers([
        handler("pz", "s"),
        handler("login", "s"),
        handler("userEdit", "s"),
        handler("todoX", "s"),
      ])
    ).toEqual([
      '    dynamic extension.background "Message_Processing_Flow" "Shows message processing flow through handlers and services" {',
      '    dynamic extension.background "Authentication_Flow" "Shows authentication request processing and service interactions" {',
      '    dynamic extension.background "User_Management_Flow" "Shows user management operations and service dependencies" {',
      '    dynamic extension.background "Todo_Management_Flow" "Shows todo item operations and service dependencies" {',
    ]);
  });
});

describe("deployment environments", () => {
  const DEP: StructurizrDSLOptions = { ...QUIET };

  test("nodes without an environment tag deploy every container to Production", () => {
    const dsl = generateStructurizrDSL(analysisWith({ contextTypes: ["background", "popup"] }), {
      ...DEP,
      deploymentNodes: [{ name: "Browser" }],
    });
    expect(deploymentModel(dsl)).toBe(
      [
        '    deploymentEnvironment "Production" {',
        '      deploymentNode "Browser" {',
        "        containerInstance extension.background",
        "        containerInstance extension.popup",
        "      }",
        "    }",
      ].join("\n")
    );
  });

  test("nodes group by environment tag; tags, properties, children and instances render", () => {
    const nodes: DeploymentNode[] = [
      {
        name: 'Chrome "Stable"',
        description: 'The "browser"',
        technology: 'Chrome "120"',
        tags: ["Environment:Staging", "Browser", "Edge"],
        properties: { 'ver"sion': 'v"1', region: "eu" },
        containerInstances: [
          { container: "background", instances: 3 },
          { container: "popup", instances: 1 },
          { container: "content" },
        ],
      },
      {
        name: "Server",
        tags: ["environment:Production"],
        children: [
          {
            name: "Pod",
            tags: ["environment:Ignored"],
            containerInstances: [{ container: "background", instances: 2 }],
          },
          { name: "Leaf" },
        ],
      },
      { name: "Second staging", tags: ["environment:Staging"], containerInstances: [] },
    ];
    const dsl = generateStructurizrDSL(
      analysisWith({ contextTypes: ["background", "popup", "content"] }),
      { ...DEP, deploymentNodes: nodes }
    );
    expect(deploymentModel(dsl)).toBe(
      [
        '    deploymentEnvironment "Staging" {',
        '      deploymentNode "Chrome \\"Stable\\"" "The \\"browser\\"" "Chrome \\"120\\"" {',
        '        tags "Browser" "Edge"',
        "        properties {",
        '          "ver\\"sion" "v\\"1"',
        '          "region" "eu"',
        "        }",
        "        containerInstance extension.background 3",
        "        containerInstance extension.popup",
        "        containerInstance extension.content",
        "      }",
        '      deploymentNode "Second staging" {',
        "        containerInstance extension.background",
        "        containerInstance extension.popup",
        "        containerInstance extension.content",
        "      }",
        "    }",
        '    deploymentEnvironment "Production" {',
        '      deploymentNode "Server" {',
        '        deploymentNode "Pod" {',
        "          containerInstance extension.background 2",
        "        }",
        '        deploymentNode "Leaf" {',
        "          containerInstance extension.background",
        "          containerInstance extension.popup",
        "          containerInstance extension.content",
        "        }",
        "      }",
        "    }",
      ].join("\n")
    );
    // One deployment view per environment, in first-seen order.
    expect(viewsOf(dsl)).toBe(
      [
        "  views {",
        SYSTEM_CONTEXT,
        CONTAINERS,
        deploymentView("Staging"),
        deploymentView("Production"),
        EMPTY_STYLES,
        "  }",
        "}",
      ].join("\n\n")
    );
  });

  test("description-only and technology-only nodes render one quoted field", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...DEP,
      deploymentNodes: [
        { name: "A", description: "desc", containerInstances: [{ container: "background" }] },
        { name: "B", technology: "tech", containerInstances: [{ container: "background" }] },
      ],
    });
    expect(deploymentModel(dsl)).toBe(
      [
        '    deploymentEnvironment "Production" {',
        '      deploymentNode "A" "desc" {',
        "        containerInstance extension.background",
        "      }",
        '      deploymentNode "B" "tech" {',
        "        containerInstance extension.background",
        "      }",
        "    }",
      ].join("\n")
    );
  });

  test("a node whose only tag is the environment, and empty properties, adds no lines", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...DEP,
      deploymentNodes: [
        {
          name: "Only env",
          tags: ["environment:Dev"],
          properties: {},
          children: [],
          containerInstances: [{ container: "background", instances: 0 }],
        },
        { name: "Empty tags", tags: [], containerInstances: [{ container: "background" }] },
      ],
    });
    expect(deploymentModel(dsl)).toBe(
      [
        '    deploymentEnvironment "Dev" {',
        '      deploymentNode "Only env" {',
        "        containerInstance extension.background",
        "      }",
        "    }",
        '    deploymentEnvironment "Production" {',
        '      deploymentNode "Empty tags" {',
        "        containerInstance extension.background",
        "      }",
        "    }",
      ].join("\n")
    );
  });

  test("the environment tag is found among other tags, not only first", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...DEP,
      deploymentNodes: [
        {
          name: "N",
          tags: ["Browser", "environment:Staging"],
          containerInstances: [{ container: "background" }],
        },
      ],
    });
    expect(deploymentModel(dsl)).toBe(
      [
        '    deploymentEnvironment "Staging" {',
        '      deploymentNode "N" {',
        '        tags "Browser"',
        "        containerInstance extension.background",
        "      }",
        "    }",
      ].join("\n")
    );
    expect(viewsOf(dsl)).toContain(deploymentView("Staging"));
    expect(dsl).not.toContain('"Production"');
  });

  test("an empty children list still gets the all-containers fallback", () => {
    const dsl = generateStructurizrDSL(analysisWith({ contextTypes: ["background", "popup"] }), {
      ...DEP,
      deploymentNodes: [{ name: "N", children: [] }],
    });
    expect(deploymentModel(dsl)).toBe(
      [
        '    deploymentEnvironment "Production" {',
        '      deploymentNode "N" {',
        "        containerInstance extension.background",
        "        containerInstance extension.popup",
        "      }",
        "    }",
      ].join("\n")
    );
  });

  test("a deployment environment name with spaces gets a sanitised view key", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...DEP,
      deploymentNodes: [{ name: "N", tags: ["environment:Pre Prod"] }],
    });
    expect(dsl).toContain(
      '    deployment extension "Pre Prod" "Pre_Prod" "Pre Prod environment deployment architecture" {\n      title "Pre Prod"'
    );
  });
});

describe("generateStyles", () => {
  test("a theme renders even without default styles", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      ...QUIET,
      styles: { theme: "https://example.test/theme.json" },
    });
    expect(viewsOf(dsl)).toBe(
      [
        "  views {",
        SYSTEM_CONTEXT,
        CONTAINERS,
        "    styles {\n      theme https://example.test/theme.json\n    }",
        "  }",
        "}",
      ].join("\n\n")
    );
  });

  test("default styles render element styles then relationship styles", () => {
    const dsl = generateStructurizrDSL(analysisWith(), {
      includeComponentDiagrams: false,
      includeDynamicDiagrams: false,
      styles: {
        elements: { Custom: { shape: "Box" } },
        relationships: { Wire: { thickness: 7 } },
      },
    });
    const styles = dsl.slice(dsl.indexOf("    styles {"), dsl.lastIndexOf("\n    }\n\n  }") + 6);
    expect(styles.startsWith("    styles {\n      element ")).toBe(true);
    expect(
      styles.endsWith('      relationship "Wire" {\n        thickness 7\n      }\n    }')
    ).toBe(true);
    expect(styles).toContain('      element "Custom" {\n        shape Box\n      }');
    const lastElement = styles.lastIndexOf("      element ");
    const firstRelationship = styles.indexOf("      relationship ");
    expect(lastElement).toBeLessThan(firstRelationship);
    expect(styles).not.toContain("theme");
  });
});
