import { describe, expect, test } from "bun:test";
import type { ArchitectureAnalysis } from "../../../analysis/src/types/architecture";
import type { MessageHandler } from "../../../analysis/src/types/core";
import { generateStructurizrDSL } from "../codegen/structurizr";

// The message-type classifiers (inferHandlerCategory, isStateHandler,
// isQueryHandler) are private, so these tests read them through the DSL they
// shape: the title of the auto-generated dynamic view a handler lands in, and
// the implicit "Updates state" edges between state and query handlers.

function handler(messageType: string, relationTo?: string): MessageHandler {
  return {
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: "background.ts", line: 1 },
    messageType,
    ...(relationTo
      ? {
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
        }
      : {}),
  };
}

function analysisWith(handlers: MessageHandler[]): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "Test Extension", version: "1.0.0", description: "Test" },
    contexts: {
      background: {
        type: "background",
        entryPoint: "background.ts",
        handlers,
        chromeAPIs: [],
        externalAPIs: [],
        dependencies: [],
      },
    },
    messageFlows: [],
    integrations: [],
  };
}

/** Titles of the dynamic views, in output order. */
function dynamicTitles(dsl: string): string[] {
  const titles: string[] = [];
  const blocks = dsl.split(/\n\s*dynamic /).slice(1);
  for (const block of blocks) {
    const match = block.match(/\n\s*title "([^"]+)"/);
    if (match?.[1]) titles.push(match[1]);
  }
  return titles;
}

/** Title of the dynamic view that holds the step for `messageType`. */
function viewTitleFor(dsl: string, messageType: string): string | undefined {
  const blocks = dsl.split(/\n\s*dynamic /).slice(1);
  const block = blocks.find((b) => b.includes(`"step ${messageType}"`));
  return block?.match(/\n\s*title "([^"]+)"/)?.[1];
}

/**
 * The category title `messageType` gets. Five neutral fillers push the
 * handler count past the combined-diagram limit (5), so every category gets
 * its own view; the target is first, so its view is never cut by the
 * five-view cap.
 */
function categoryTitleOf(messageType: string): string | undefined {
  const fillers = ["pz1", "pz2", "pz3", "pz4", "pz5"].map((t) => handler(t, "svc"));
  const dsl = generateStructurizrDSL(analysisWith([handler(messageType, "svc"), ...fillers]));
  return viewTitleFor(dsl, messageType);
}

describe("handler category inference (dynamic view titles)", () => {
  const cases: Array<[string, string]> = [
    ["authThing", "Authentication Flow"],
    ["loginThing", "Authentication Flow"],
    ["logoutThing", "Authentication Flow"],
    ["verifyThing", "Authentication Flow"],
    ["registerThing", "Authentication Flow"],
    ["LOGIN", "Authentication Flow"],
    ["userThing", "User Management Flow"],
    ["todoThing", "Todo Management Flow"],
    ["queryThing", "Query Processing Flow"],
    ["getThing", "Query Processing Flow"],
    ["fetchThing", "Query Processing Flow"],
    ["listThing", "Query Processing Flow"],
    ["commandThing", "Command Processing Flow"],
    ["createThing", "Command Processing Flow"],
    ["updateThing", "Command Processing Flow"],
    ["deleteThing", "Command Processing Flow"],
    ["addThing", "Command Processing Flow"],
    ["removeThing", "Command Processing Flow"],
    ["pingThing", "Message Processing Flow"],
  ];

  for (const [messageType, title] of cases) {
    test(`${messageType} → ${title}`, () => {
      expect(categoryTitleOf(messageType)).toBe(title);
    });
  }

  test("earlier categories win when a type matches several", () => {
    expect(categoryTitleOf("authUser")).toBe("Authentication Flow");
    expect(categoryTitleOf("userTodo")).toBe("User Management Flow");
    expect(categoryTitleOf("todoGet")).toBe("Todo Management Flow");
    expect(categoryTitleOf("getAdd")).toBe("Query Processing Flow");
  });
});

describe("combined vs separate dynamic views", () => {
  test("5 handlers in 3 categories share one combined view", () => {
    const dsl = generateStructurizrDSL(
      analysisWith([
        handler("getA", "svc"),
        handler("getB", "svc"),
        handler("addA", "svc"),
        handler("addB", "svc"),
        handler("loginA", "svc"),
      ])
    );
    expect(dynamicTitles(dsl)).toEqual(["Message Processing Flow"]);
  });

  test("6 handlers in one category get a view of their own", () => {
    const dsl = generateStructurizrDSL(
      analysisWith(["getA", "getB", "getC", "getD", "getE", "getF"].map((t) => handler(t, "svc")))
    );
    expect(dynamicTitles(dsl)).toEqual(["Query Processing Flow"]);
  });

  test("4 categories split even with only 4 handlers", () => {
    const dsl = generateStructurizrDSL(
      analysisWith([
        handler("getA", "svc"),
        handler("addA", "svc"),
        handler("loginA", "svc"),
        handler("todoA", "svc"),
      ])
    );
    expect(dynamicTitles(dsl)).toEqual([
      "Query Processing Flow",
      "Command Processing Flow",
      "Authentication Flow",
      "Todo Management Flow",
    ]);
  });

  test("at most 5 category views", () => {
    const dsl = generateStructurizrDSL(
      analysisWith([
        handler("loginA", "svc"),
        handler("userA", "svc"),
        handler("todoA", "svc"),
        handler("getA", "svc"),
        handler("addA", "svc"),
        handler("pingA", "svc"),
      ])
    );
    expect(dynamicTitles(dsl)).toEqual([
      "Authentication Flow",
      "User Management Flow",
      "Todo Management Flow",
      "Query Processing Flow",
      "Command Processing Flow",
    ]);
  });

  test("handlers without relationships produce no auto view", () => {
    const dsl = generateStructurizrDSL(analysisWith([handler("getA"), handler("addA")]));
    expect(dynamicTitles(dsl)).toEqual([]);
  });
});

describe("state/query classification (implicit 'Updates state' edges)", () => {
  function stateEdges(types: string[]): number {
    const dsl = generateStructurizrDSL(analysisWith(types.map((t) => handler(t))));
    return dsl.split('"Updates state"').length - 1;
  }

  const stateWords = [
    "add",
    "create",
    "update",
    "delete",
    "remove",
    "toggle",
    "clear",
    "login",
    "logout",
  ];
  for (const word of stateWords) {
    test(`${word}Thing is a state handler`, () => {
      expect(stateEdges([`${word}Thing`, "getThing"])).toBe(1);
    });
  }

  for (const word of ["get", "fetch", "load"]) {
    test(`${word}Thing is a query handler`, () => {
      expect(stateEdges(["addThing", `${word}Thing`])).toBe(1);
    });
  }

  test("a type that is neither makes no edge", () => {
    expect(stateEdges(["pingThing", "getThing"])).toBe(0);
    expect(stateEdges(["addThing", "pingThing"])).toBe(0);
  });

  test("a state handler is never also a query handler", () => {
    // updateLoad matches both lists; it counts as state only, so two state
    // handlers × one query handler = 2 edges, not 3.
    expect(stateEdges(["updateLoad", "addThing", "getThing"])).toBe(2);
  });

  test("the edge runs from the state handler to the query handler", () => {
    const dsl = generateStructurizrDSL(analysisWith([handler("addThing"), handler("getThing")]));
    expect(dsl).toContain(
      [
        '        addthing_handler -> getthing_handler "Updates state" {',
        '          tags "Implicit"',
        "        }",
      ].join("\n")
    );
  });
});
