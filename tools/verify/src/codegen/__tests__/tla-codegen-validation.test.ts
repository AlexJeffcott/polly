import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import { TLAGenerator } from "../tla";

/**
 * Tests to ensure TLA+ code generation rejects invalid TLA+ identifiers
 * from message types. This prevents the bug from issue #11 where invalid
 * TypeScript type syntax makes it through to TLA+ generation.
 */
describe("TLA+ Code Generation Validation", () => {
  const mockConfig: VerificationConfig = {
    state: {
      connected: { type: "enum", values: ["true", "false"] },
    },
    messages: {
      maxInFlight: 3,
      maxTabs: 1,
    },
    onBuild: "warn",
    onRelease: "error",
  };

  test("should not generate handlers for message types with invalid TLA+ identifiers", async () => {
    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: [
        // Valid types
        "query",
        "command",
        // Invalid types that somehow got through
        "{ ok: true; value: t }",
        "{ ok: false; error: e }",
      ],
      fields: [],
      handlers: [
        {
          messageType: "query",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 1 },
        },
        {
          messageType: "command",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 2 },
        },
        // These should be filtered out during codegen!
        {
          messageType: "{ ok: true; value: t }",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 3 },
        },
        {
          messageType: "{ ok: false; error: e }",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 4 },
        },
      ],
    };

    const generator = new TLAGenerator();

    // Should throw an error for invalid message types
    await expect(async () => {
      await generator.generate(mockConfig, analysis);
    }).toThrow(/Invalid message type.*TLA\+ identifiers must start with a letter/);
  });

  test("should only include valid message types in UserMessageTypes set", async () => {
    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: [
        "authenticate",
        "query",
        "command",
        // Invalid types (should cause error)
        "{ ok: true; value: t }",
        "{ ok: false; error: e }",
        "123invalid", // starts with number
        "has-dash",
        "has.dot",
        "has:colon",
      ],
      fields: [],
      handlers: [],
    };

    const generator = new TLAGenerator();

    // Should throw an error for invalid message types
    await expect(async () => {
      await generator.generate(mockConfig, analysis);
    }).toThrow(/Invalid message type/);
  });

  test("should handle edge cases in message type names", async () => {
    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: [
        // Valid edge cases
        "a",
        "A",
        "message123",
        "MESSAGE_TYPE",
        "message_type_with_underscores",
        // Invalid edge cases
        "",
        " ",
        "123",
        "!invalid",
        "in valid",
        "in-valid",
        "in.valid",
        "in:valid",
        "in;valid",
        "in,valid",
        "in{valid",
        "in}valid",
        "in[valid",
        "in]valid",
        "in(valid",
        "in)valid",
      ],
      fields: [],
      handlers: [],
    };

    const generator = new TLAGenerator();

    // Should throw an error for invalid message types
    await expect(async () => {
      await generator.generate(mockConfig, analysis);
    }).toThrow(/Invalid message type/);
  });

  test("should validate TLA+ identifier in messageTypeToActionName", async () => {
    const generator = new TLAGenerator();

    // Access the private method via type assertion for testing
    const messageTypeToActionName = (generator as any).messageTypeToActionName.bind(generator);

    // Valid identifiers should work (converted to PascalCase)
    expect(messageTypeToActionName("query")).toBe("HandleQuery");
    expect(messageTypeToActionName("user_login")).toBe("HandleUserLogin");
    expect(messageTypeToActionName("API_REQUEST")).toBe("HandleApiRequest");

    // Invalid identifiers should NOT produce invalid TLA+ (this test will fail before fix)
    // After fix, these should either:
    // 1. Be filtered out before reaching this method, OR
    // 2. Return a sanitized/valid identifier, OR
    // 3. Return null/undefined to indicate invalid input
    const invalidResult1 = messageTypeToActionName("{ ok: true; value: t }");
    const invalidResult2 = messageTypeToActionName("has-dash");
    const invalidResult3 = messageTypeToActionName("has.dot");

    // These should NOT create invalid TLA+ identifiers
    // They should not contain special characters
    if (invalidResult1) {
      expect(invalidResult1).toMatch(/^Handle[a-zA-Z][a-zA-Z0-9_]*$/);
    }
    if (invalidResult2) {
      expect(invalidResult2).toMatch(/^Handle[a-zA-Z][a-zA-Z0-9_]*$/);
    }
    if (invalidResult3) {
      expect(invalidResult3).toMatch(/^Handle[a-zA-Z][a-zA-Z0-9_]*$/);
    }
  });
});
