import { describe, expect, test } from "bun:test";
import type { ArchitectureAnalysis } from "../../../analysis/src/types/architecture";
import type { MessageHandler } from "../../../analysis/src/types/core";
import { generateStructurizrDSL } from "../codegen/structurizr";

// generateComponentDescription, getComponentTags and getComponentProperties
// are private, so these tests read them through the component block each
// handler becomes in the DSL: its description string, its `tags` line and its
// `properties` block.

interface HandlerOpts {
  file?: string;
  line?: number;
  noLocation?: boolean;
}

function handler(messageType: string, opts: HandlerOpts = {}): MessageHandler {
  const h: MessageHandler = {
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: opts.file ?? "/test/src/background.ts", line: opts.line ?? 42 },
    messageType,
  };
  if (opts.noLocation) {
    // A handler the analyser could not place in a file.
    Reflect.deleteProperty(h, "location");
  }
  return h;
}

function analysisWith(contextKey: string, handlers: MessageHandler[]): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "Test Extension", version: "1.0.0", description: "Test" },
    contexts: {
      [contextKey]: {
        type: contextKey,
        entryPoint: `${contextKey}.ts`,
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

interface ComponentMeta {
  description: string;
  tags: string[];
  properties: Record<string, string>;
}

/** Description, tags and properties of the one component `messageType` makes. */
function componentOf(
  messageType: string,
  opts: HandlerOpts & { context?: string } = {}
): ComponentMeta {
  const context = opts.context ?? "background";
  const dsl = generateStructurizrDSL(analysisWith(context, [handler(messageType, opts)]), {
    componentDiagramContexts: [context],
  });
  const lines = dsl.split("\n");
  const start = lines.findIndex((l) => /^\s*\S+ = component "[^"]*" "[^"]*" \{$/.test(l));
  if (start < 0) throw new Error(`no component in DSL:\n${dsl}`);
  const header = lines[start] ?? "";
  const description = header.match(/= component "[^"]*" "([^"]*)" \{$/)?.[1] ?? "";

  // The component block runs to the first line closed at the header's indent.
  const indent = header.match(/^\s*/)?.[0] ?? "";
  const close = lines.indexOf(`${indent}}`, start);
  const body = lines.slice(start + 1, close).map((l) => l.trim());

  const tagLine = body.find((l) => l.startsWith("tags ")) ?? "";
  const tags = [...tagLine.matchAll(/"([^"]*)"/g)].map((m) => m[1] ?? "");

  const properties: Record<string, string> = {};
  for (const m of body.map((l) => l.match(/^"([^"]*)" "([^"]*)"$/))) {
    if (m?.[1] !== undefined && m[2] !== undefined) properties[m[1]] = m[2];
  }
  return { description, tags, properties };
}

const descriptionOf = (t: string) => componentOf(t).description;
const tagsOf = (t: string) => componentOf(t).tags;
const propsOf = (t: string, opts: HandlerOpts & { context?: string } = {}) =>
  componentOf(t, opts).properties;

describe("component description", () => {
  const cases: Array<[string, string]> = [
    ["user_login", "Authenticates users and establishes sessions"],
    ["LOGIN", "Authenticates users and establishes sessions"],
    ["user_logout", "Terminates user sessions and clears credentials"],
    ["LOGOUT", "Terminates user sessions and clears credentials"],
    // CRUD: the `_verb` is cut out and remaining underscores become spaces.
    ["todo_add", "Creates new todo items and persists to storage"],
    ["todo_create", "Creates new todo items and persists to storage"],
    ["TODO_ITEM_ADD", "Creates new todo item items and persists to storage"],
    ["shopping_list_item_create", "Creates new shopping list item items and persists to storage"],
    ["addtodo", "Creates new addtodo items and persists to storage"],
    ["todo_add_extra", "Creates new todo extra items and persists to storage"],
    ["todo_remove", "Removes todo items from storage"],
    ["todo_delete", "Removes todo items from storage"],
    ["TODO_ITEM_DELETE", "Removes todo item items from storage"],
    ["deletetodo", "Removes deletetodo items from storage"],
    ["todo_update", "Updates todo item state and syncs with storage"],
    ["todo_toggle", "Updates todo item state and syncs with storage"],
    ["TODO_ITEM_TOGGLE", "Updates todo item item state and syncs with storage"],
    ["toggletodo", "Updates toggletodo item state and syncs with storage"],
    ["todo_clear", "Clears all todo items matching criteria"],
    ["todo_list_clear_completed", "Clears all todo list items matching criteria"],
    ["cleartodo", "Clears all cleartodo items matching criteria"],
    ["todo_get", "Retrieves todo data from storage"],
    ["todo_fetch", "Retrieves todo data from storage"],
    ["todo_load", "Retrieves todo data from storage"],
    ["TODO_ITEM_FETCH", "Retrieves todo item data from storage"],
    ["gettodo", "Retrieves gettodo data from storage"],
    // Default keeps the original casing.
    ["PING_Server", "Processes PING_Server messages and coordinates business logic"],
  ];
  for (const [messageType, description] of cases) {
    test(`${messageType} → ${description}`, () => {
      expect(descriptionOf(messageType)).toBe(description);
    });
  }

  test("earlier rules win when a type matches several", () => {
    expect(descriptionOf("login_logout")).toBe("Authenticates users and establishes sessions");
    expect(descriptionOf("logout_add")).toBe("Terminates user sessions and clears credentials");
    expect(descriptionOf("x_add_remove")).toBe(
      "Creates new x remove items and persists to storage"
    );
    expect(descriptionOf("x_remove_update")).toBe("Removes x update items from storage");
    expect(descriptionOf("x_update_clear")).toBe(
      "Updates x clear item state and syncs with storage"
    );
    expect(descriptionOf("x_clear_get")).toBe("Clears all x items matching criteria");
  });

  test("only the first verb occurrence is cut", () => {
    expect(descriptionOf("a_add_b_add")).toBe("Creates new a b add items and persists to storage");
    expect(descriptionOf("a_get_b_get")).toBe("Retrieves a b get data from storage");
  });
});

describe("component tags", () => {
  const cases: Array<[string, string[]]> = [
    ["ping", ["Message Handler"]],
    ["login", ["Message Handler", "Authentication"]],
    ["logout", ["Message Handler", "Authentication"]],
    ["auth", ["Message Handler", "Authentication"]],
    ["AUTH", ["Message Handler", "Authentication"]],
    ["add", ["Message Handler", "CRUD"]],
    ["create", ["Message Handler", "CRUD"]],
    ["update", ["Message Handler", "CRUD"]],
    ["delete", ["Message Handler", "CRUD"]],
    ["remove", ["Message Handler", "CRUD"]],
    ["toggle", ["Message Handler", "CRUD"]],
    ["TOGGLE", ["Message Handler", "CRUD"]],
    ["get", ["Message Handler", "Query"]],
    ["fetch", ["Message Handler", "Query"]],
    ["load", ["Message Handler", "Query"]],
    ["LOAD", ["Message Handler", "Query"]],
    ["user", ["Message Handler", "User Management"]],
    ["USER", ["Message Handler", "User Management"]],
    ["todo", ["Message Handler", "Todo Management"]],
    ["TODO", ["Message Handler", "Todo Management"]],
    ["state", ["Message Handler", "State Management"]],
    ["STATE", ["Message Handler", "State Management"]],
  ];
  for (const [messageType, tags] of cases) {
    test(`${messageType} → ${tags.join(", ")}`, () => {
      expect(tagsOf(messageType)).toEqual(tags);
    });
  }

  test("only one functional tag, the earliest that matches", () => {
    expect(tagsOf("login_add_get")).toEqual(["Message Handler", "Authentication"]);
    expect(tagsOf("add_get")).toEqual(["Message Handler", "CRUD"]);
  });

  test("domain tags stack after the functional tag, in fixed order", () => {
    expect(tagsOf("state_todo_user_get")).toEqual([
      "Message Handler",
      "Query",
      "User Management",
      "Todo Management",
      "State Management",
    ]);
    expect(tagsOf("user_auth")).toEqual(["Message Handler", "Authentication", "User Management"]);
  });
});

describe("component properties", () => {
  test("Source is the file relative to the project root, with the line", () => {
    expect(propsOf("ping", { file: "/test/src/bg.ts", line: 7 })["Source"]).toBe("src/bg.ts:7");
  });

  test("Source keeps a file outside the project root as is", () => {
    expect(propsOf("ping", { file: "/testing/bg.ts", line: 3 })["Source"]).toBe("/testing/bg.ts:3");
  });

  test("no location means no Source and plain TypeScript", () => {
    expect(propsOf("ping", { noLocation: true })).toEqual({
      Technology: "TypeScript",
      Pattern: "Message Handler",
    });
  });

  test("no location in a server context still detects WebSocket", () => {
    expect(propsOf("ping", { noLocation: true, context: "server" })).toEqual({
      Technology: "TypeScript, WebSocket",
      Pattern: "Message Handler",
    });
  });

  const techCases: Array<[string, string, string]> = [
    ["/test/src/bg.ts", "background", "TypeScript"],
    ["/test/src/ws.ts", "background", "TypeScript, WebSocket"],
    ["/test/src/bg.ts", "server", "TypeScript, WebSocket"],
    ["/test/src/socket.io.ts", "background", "TypeScript, Socket.IO"],
    ["/test/src/elysia.ts", "background", "TypeScript, Elysia"],
    ["/test/ws/socket.io/elysia.ts", "background", "TypeScript, WebSocket, Socket.IO, Elysia"],
  ];
  for (const [file, context, technology] of techCases) {
    test(`Technology for ${file} in ${context} is "${technology}"`, () => {
      expect(propsOf("ping", { file, context })["Technology"]).toBe(technology);
    });
  }

  test("full block for a plain handler, in key order", () => {
    const props = propsOf("ping", { file: "/test/src/bg.ts", line: 1 });
    expect(Object.entries(props)).toEqual([
      ["Source", "src/bg.ts:1"],
      ["Technology", "TypeScript"],
      ["Pattern", "Message Handler"],
    ]);
  });

  const patternCases: Array<[string, string, string]> = [
    ["query", "Query Handler", "Query"],
    ["get", "Query Handler", "Query"],
    ["fetch", "Query Handler", "Query"],
    ["load", "Query Handler", "Query"],
    ["QUERY", "Query Handler", "Query"],
    ["command", "Command Handler", "Command"],
    ["add", "Command Handler", "Command"],
    ["create", "Command Handler", "Command"],
    ["update", "Command Handler", "Command"],
    ["delete", "Command Handler", "Command"],
    ["remove", "Command Handler", "Command"],
    ["auth", "Authentication Handler", "Authentication"],
    ["login", "Authentication Handler", "Authentication"],
    ["logout", "Authentication Handler", "Authentication"],
    ["subscribe", "Subscription Handler", "Subscription"],
    ["watch", "Subscription Handler", "Subscription"],
    ["listen", "Subscription Handler", "Subscription"],
  ];
  for (const [messageType, pattern, kind] of patternCases) {
    test(`${messageType} → ${pattern} / ${kind}`, () => {
      expect(Object.entries(propsOf(messageType, { file: "/test/src/bg.ts", line: 1 }))).toEqual([
        ["Source", "src/bg.ts:1"],
        ["Technology", "TypeScript"],
        ["Message Type", kind],
        ["Pattern", pattern],
      ]);
    });
  }

  test("toggle is not a command pattern", () => {
    expect(propsOf("toggle")["Pattern"]).toBe("Message Handler");
    expect(propsOf("toggle")["Message Type"]).toBeUndefined();
  });

  test("earlier patterns win when a type matches several", () => {
    expect(propsOf("get_add")["Pattern"]).toBe("Query Handler");
    expect(propsOf("add_login")["Pattern"]).toBe("Command Handler");
    expect(propsOf("login_watch")["Pattern"]).toBe("Authentication Handler");
  });
});
