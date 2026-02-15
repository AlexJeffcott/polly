// Round-Trip Validation Tests - ensures generated TLA+ preserves all information
// 40 comprehensive tests for RoundTripValidator class

import { describe, expect, test } from "bun:test";
import { RoundTripValidator } from "../../codegen/round-trip";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";

describe("Round-Trip Validation", () => {
  const validator = new RoundTripValidator();

  // Helper to create minimal config
  const createConfig = (state: Record<string, any>): VerificationConfig => ({
    state,
    messages: { maxInFlight: 3, maxTabs: 1 },
    onBuild: "warn" as const,
    onRelease: "error" as const,
  });

  // Helper to create minimal analysis
  const createAnalysis = (
    messageTypes: string[],
    handlers: Array<{ messageType: string }>
  ): CodebaseAnalysis => ({
    stateType: null,
    messageTypes,
    fields: [],
    handlers: handlers.map((h) => ({
      ...h,
      node: "background" as const,
      assignments: [],
      preconditions: [],
      postconditions: [],
      location: { file: "test.ts", line: 1 },
    })),
  });

  // ============================================================================
  // MESSAGE TYPE EXTRACTION (10 tests)
  // ============================================================================

  describe("Message Type Extraction", () => {
    test("extracts single message type", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0", "1"] } });
      const analysis = createAnalysis(["query"], [{ messageType: "query" }]);
      const spec = `UserMessageTypes == {"query"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toContain("query");
    });

    test("extracts multiple message types", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(
        ["query", "command", "subscribe"],
        [{ messageType: "query" }, { messageType: "command" }, { messageType: "subscribe" }]
      );
      const spec = `UserMessageTypes == {"query", "command", "subscribe"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toHaveLength(3);
      expect(result.extracted.messageTypes).toContain("query");
      expect(result.extracted.messageTypes).toContain("command");
      expect(result.extracted.messageTypes).toContain("subscribe");
    });

    test("handles empty message types set", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = "UserMessageTypes == {}";

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toHaveLength(0);
    });

    test("detects missing message type", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query", "command"], []);
      const spec = `UserMessageTypes == {"query"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      expect(
        result.errors.some((e) => e.component === "message-type" && e.type === "missing")
      ).toBe(true);
    });

    test("detects extra message type", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query"], []);
      const spec = `UserMessageTypes == {"query", "extra"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      expect(result.errors.some((e) => e.component === "message-type" && e.type === "extra")).toBe(
        true
      );
    });

    test("handles message types with underscores", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["user_login", "api_request"], []);
      const spec = `UserMessageTypes == {"user_login", "api_request"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toContain("user_login");
      expect(result.extracted.messageTypes).toContain("api_request");
    });

    test("handles message types in any order", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["a", "b", "c"], []);
      const spec = `
UserMessageTypes == {"c", "a", "b"}
State == [contextStates: [ctx |-> [count: 0]]]
InitialState == TRUE
StateTransition == TRUE
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(true);
    });

    test("handles message types with special formatting", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query"], []);
      const spec = `
UserMessageTypes == {
  "query"
}
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toContain("query");
    });

    test("handles CamelCase message types", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["UserLogin", "ApiRequest"], []);
      const spec = `UserMessageTypes == {"UserLogin", "ApiRequest"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toContain("UserLogin");
      expect(result.extracted.messageTypes).toContain("ApiRequest");
    });

    test("handles message types with numbers", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["msg1", "msg2", "msg3"], []);
      const spec = `UserMessageTypes == {"msg1", "msg2", "msg3"}`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.messageTypes).toHaveLength(3);
    });
  });

  // ============================================================================
  // STATE FIELD EXTRACTION (10 tests)
  // ============================================================================

  describe("State Field Extraction", () => {
    test("extracts single state field", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [count: 0]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.stateFields).toContain("count");
    });

    test("extracts multiple state fields", async () => {
      const config = createConfig({
        count: { type: "enum", values: ["0"] },
        active: { type: "enum", values: ["true", "false"] },
        name: { maxLength: 100 },
      });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [count: 0, active: TRUE, name: ""]]]
InitialState == TRUE
StateTransition == TRUE
`;

      const result = await validator.validate(config, analysis, spec);

      // May extract contextStates as well
      expect(result.extracted.stateFields.length).toBeGreaterThanOrEqual(3);
      expect(result.extracted.stateFields).toContain("count");
      expect(result.extracted.stateFields).toContain("active");
      expect(result.extracted.stateFields).toContain("name");
    });

    test("detects missing state field", async () => {
      const config = createConfig({
        count: { type: "enum", values: ["0"] },
        missing: { type: "enum", values: ["0"] },
      });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [count: 0]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      expect(result.errors.some((e) => e.component === "state-field" && e.type === "missing")).toBe(
        true
      );
    });

    test("allows extra state fields (metadata)", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [count: 0, metadata: "extra"]]]
`;

      const result = await validator.validate(config, analysis, spec);

      // Extra fields are okay
      expect(result.extracted.stateFields).toContain("count");
      expect(result.extracted.stateFields).toContain("metadata");
    });

    test("handles fields with underscores", async () => {
      const config = createConfig({
        user_count: { type: "enum", values: ["0"] },
        api_status: { type: "enum", values: ["active"] },
      });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [user_count: 0, api_status: "active"]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.stateFields).toContain("user_count");
      expect(result.extracted.stateFields).toContain("api_status");
    });

    test("handles CamelCase field names", async () => {
      const config = createConfig({
        userCount: { type: "enum", values: ["0"] },
        apiStatus: { type: "enum", values: ["active"] },
      });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [userCount: 0, apiStatus: "active"]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.stateFields).toContain("userCount");
      expect(result.extracted.stateFields).toContain("apiStatus");
    });

    test("handles multiline state definition", async () => {
      const config = createConfig({
        count: { type: "enum", values: ["0"] },
        active: { type: "enum", values: ["true"] },
      });
      const analysis = createAnalysis([], []);
      const spec = `
State == [
  contextStates: [
    ctx |-> [
      count: 0,
      active: TRUE
    ]
  ]
]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.stateFields).toContain("count");
      expect(result.extracted.stateFields).toContain("active");
    });

    test("extracts fields from direct State record", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
State == [count: 0, active: TRUE]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.stateFields).toContain("count");
    });

    test("handles empty state", async () => {
      const config = createConfig({});
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [:]]]
InitialState == TRUE
StateTransition == TRUE
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(true);
    });

    test("handles complex nested state", async () => {
      const config = createConfig({
        count: { type: "enum", values: ["0"] },
        items: { maxSize: 10 },
      });
      const analysis = createAnalysis([], []);
      const spec = `
State == [contextStates: [ctx |-> [
  count: 0,
  items: <<>>
]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.stateFields).toContain("count");
      expect(result.extracted.stateFields).toContain("items");
    });
  });

  // ============================================================================
  // HANDLER EXTRACTION (10 tests)
  // ============================================================================

  describe("Handler Extraction", () => {
    test("extracts single handler", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query"], [{ messageType: "query" }]);
      const spec = `
HandleQuery(ctx) ==
  /\\ UNCHANGED contextStates
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("Query");
    });

    test("extracts multiple handlers", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(
        ["query", "command", "subscribe"],
        [{ messageType: "query" }, { messageType: "command" }, { messageType: "subscribe" }]
      );
      const spec = `
HandleQuery(ctx) == /\\ UNCHANGED contextStates
HandleCommand(ctx) == /\\ UNCHANGED contextStates
HandleSubscribe(ctx) == /\\ UNCHANGED contextStates
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toHaveLength(3);
      expect(result.extracted.handlers).toContain("Query");
      expect(result.extracted.handlers).toContain("Command");
      expect(result.extracted.handlers).toContain("Subscribe");
    });

    test("detects missing handler", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(
        ["query", "command"],
        [{ messageType: "query" }, { messageType: "command" }]
      );
      const spec = `
HandleQuery(ctx) == /\\ UNCHANGED contextStates
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      expect(result.errors.some((e) => e.component === "handler" && e.type === "missing")).toBe(
        true
      );
    });

    test("handles snake_case to PascalCase conversion", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["user_login"], [{ messageType: "user_login" }]);
      const spec = `
UserMessageTypes == {"user_login"}
State == [contextStates: [ctx |-> [count: 0]]]
HandleUserLogin(ctx) == /\\ UNCHANGED contextStates
InitialState == TRUE
StateTransition == TRUE
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("UserLogin");
      expect(result.valid).toBe(true);
    });

    test("handles SCREAMING_SNAKE_CASE to PascalCase conversion", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["API_REQUEST"], [{ messageType: "API_REQUEST" }]);
      const spec = `
UserMessageTypes == {"API_REQUEST"}
State == [contextStates: [ctx |-> [count: 0]]]
HandleApiRequest(ctx) == /\\ UNCHANGED contextStates
InitialState == TRUE
StateTransition == TRUE
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("ApiRequest");
      expect(result.valid).toBe(true);
    });

    test("handles camelCase to PascalCase conversion", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["apiRequest"], [{ messageType: "apiRequest" }]);
      const spec = `
HandleApiRequest(ctx) == /\\ UNCHANGED contextStates
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("ApiRequest");
    });

    test("handles multiline handler definitions", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query"], [{ messageType: "query" }]);
      const spec = `
HandleQuery(ctx) ==
  /\\ contextStates' = [contextStates EXCEPT ![ctx].count = @ + 1]
  /\\ UNCHANGED <<messages, ports>>
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("Query");
    });

    test("handles handlers with comments", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query"], [{ messageType: "query" }]);
      const spec = `
\\* This is a comment
HandleQuery(ctx) == \\* Comment here too
  /\\ UNCHANGED contextStates
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("Query");
    });

    test("handles handlers with complex bodies", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["query"], [{ messageType: "query" }]);
      const spec = `
HandleQuery(ctx) ==
  LET increment == 1
  IN /\\ contextStates' = [contextStates EXCEPT
                ![ctx].count = @ + increment]
     /\\ UNCHANGED <<messages, ports>>
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.handlers).toContain("Query");
    });

    test("validates all handlers match analyzed message types", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(
        ["query", "command"],
        [{ messageType: "query" }, { messageType: "command" }]
      );
      const spec = `
UserMessageTypes == {"query", "command"}
State == [contextStates: [ctx |-> [count: 0]]]
HandleQuery(ctx) == /\\ UNCHANGED contextStates
HandleCommand(ctx) == /\\ UNCHANGED contextStates
InitialState == TRUE
StateTransition == TRUE
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });
  });

  // ============================================================================
  // INIT/NEXT STRUCTURE (5 tests)
  // ============================================================================

  describe("Init/Next Structure", () => {
    test("detects InitialState operator", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
InitialState == /\\ contextStates = [ctx \\in Contexts |-> [count: 0]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.hasInit).toBe(true);
    });

    test("detects Init operator (alternative name)", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
Init == /\\ x = 0
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.hasInit).toBe(true);
    });

    test("detects StateTransition operator", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
StateTransition == \\/ HandleQuery(ctx)
                   \\/ UNCHANGED vars
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.hasNext).toBe(true);
    });

    test("detects Next operator (alternative name)", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
Next == x' = x + 1
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.extracted.hasNext).toBe(true);
    });

    test("reports missing Init/Next operators", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis([], []);
      const spec = `
VARIABLE x
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      expect(result.errors.some((e) => e.component === "init")).toBe(true);
      expect(result.errors.some((e) => e.component === "next")).toBe(true);
    });
  });

  // ============================================================================
  // COMPREHENSIVE VALIDATION (5 tests)
  // ============================================================================

  describe("Comprehensive Validation", () => {
    test("validates complete valid spec", async () => {
      const config = createConfig({
        count: { type: "enum", values: ["0", "1", "2"] },
        active: { type: "enum", values: ["true", "false"] },
      });
      const analysis = createAnalysis(
        ["query", "command"],
        [{ messageType: "query" }, { messageType: "command" }]
      );
      const spec = `
UserMessageTypes == {"query", "command"}

State == [contextStates: [ctx |-> [count: 0, active: TRUE]]]

InitialState == /\\ contextStates = [ctx \\in Contexts |-> [count: 0, active: TRUE]]

HandleQuery(ctx) == /\\ UNCHANGED contextStates
HandleCommand(ctx) == /\\ UNCHANGED contextStates

StateTransition == \\/ \\E ctx \\in Contexts: HandleQuery(ctx)
                   \\/ \\E ctx \\in Contexts: HandleCommand(ctx)
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    test("reports all missing components", async () => {
      const config = createConfig({
        count: { type: "enum", values: ["0"] },
        missing1: { type: "enum", values: ["0"] },
        missing2: { type: "enum", values: ["0"] },
      });
      const analysis = createAnalysis(
        ["query", "missing_type"],
        [{ messageType: "query" }, { messageType: "missing_type" }]
      );
      const spec = `
UserMessageTypes == {"query"}

State == [contextStates: [ctx |-> [count: 0]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      // Should have errors for:
      // - missing message type
      // - missing state fields (2)
      // - missing handler
      // - missing init
      // - missing next
      expect(result.errors.length).toBeGreaterThanOrEqual(6);
    });

    test("provides detailed error information", async () => {
      const config = createConfig({ count: { type: "enum", values: ["0"] } });
      const analysis = createAnalysis(["missing"], [{ messageType: "missing" }]);
      const spec = `
UserMessageTypes == {}
State == [contextStates: [ctx |-> [count: 0]]]
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(false);
      // Check error details
      const errors = result.errors;
      expect(errors.every((e) => e.message.length > 0)).toBe(true);
      expect(errors.every((e) => e.component)).toBeDefined();
      expect(errors.every((e) => e.type)).toBeDefined();
    });

    test("handles real-world complex spec", async () => {
      const config = createConfig({
        connected: { type: "enum", values: ["true", "false"] },
        authenticated: { type: "enum", values: ["true", "false"] },
        userCount: { min: 0, max: 100 },
        requestQueue: { maxSize: 10 },
      });
      const analysis = createAnalysis(
        ["authenticate", "connect", "disconnect", "request"],
        [
          { messageType: "authenticate" },
          { messageType: "connect" },
          { messageType: "disconnect" },
          { messageType: "request" },
        ]
      );
      const spec = `
UserMessageTypes == {"authenticate", "connect", "disconnect", "request"}

State == [contextStates: [ctx |-> [
  connected: FALSE,
  authenticated: FALSE,
  userCount: 0,
  requestQueue: <<>>
]]]

InitialState == /\\ contextStates = [ctx \\in Contexts |-> [
  connected: FALSE,
  authenticated: FALSE,
  userCount: 0,
  requestQueue: <<>>
]]

HandleAuthenticate(ctx) == /\\ UNCHANGED contextStates
HandleConnect(ctx) == /\\ UNCHANGED contextStates
HandleDisconnect(ctx) == /\\ UNCHANGED contextStates
HandleRequest(ctx) == /\\ UNCHANGED contextStates

StateTransition == \\/ \\E ctx \\in Contexts: HandleAuthenticate(ctx)
                   \\/ \\E ctx \\in Contexts: HandleConnect(ctx)
                   \\/ \\E ctx \\in Contexts: HandleDisconnect(ctx)
                   \\/ \\E ctx \\in Contexts: HandleRequest(ctx)
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(true);
      expect(result.extracted.messageTypes).toHaveLength(4);
      expect(result.extracted.stateFields.length).toBeGreaterThanOrEqual(4);
      expect(result.extracted.handlers).toHaveLength(4);
    });

    test("handles minimal valid spec", async () => {
      const config = createConfig({});
      const analysis = createAnalysis([], []);
      const spec = `
UserMessageTypes == {}
State == [contextStates: [ctx |-> [:]]]
InitialState == /\\ TRUE
StateTransition == /\\ UNCHANGED vars
`;

      const result = await validator.validate(config, analysis, spec);

      expect(result.valid).toBe(true);
    });
  });
});
