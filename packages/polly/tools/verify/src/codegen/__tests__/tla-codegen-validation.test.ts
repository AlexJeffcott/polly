import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import { TLAGenerator } from "../tla";

/**
 * Tests to ensure TLA+ code generation rejects message types that cannot be
 * represented as a TLA+ action. This prevents the bug from issue #11 where
 * invalid TypeScript type syntax (e.g. an inferred object-literal type) makes
 * it through to TLA+ generation.
 *
 * polly#144 narrowed "invalid": message types are emitted as quoted string
 * literals and sanitized into action names, so non-identifier types (HTTP
 * routes, dashed/dotted/colon-namespaced names) ARE representable. Only the
 * genuinely unrepresentable ones are rejected — those with no letter to seed an
 * action name, or those containing the TLA-structural characters `{}();<>=`
 * (which is what an inferred object-literal type like `{ ok: true; value: t }`
 * carries). The thrown error is "Unrepresentable message type '<type>'.".
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
        // Unrepresentable: inferred object-literal types carry `{`, `}`, `;`
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

    // Should throw for the unrepresentable object-literal message types
    await expect(async () => {
      await generator.generate(mockConfig, analysis);
    }).toThrow(/Unrepresentable message type/);
  });

  test("rejects unrepresentable message types but accepts non-identifier ones (polly#144)", async () => {
    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: [
        "authenticate",
        "query",
        "command",
        // Unrepresentable: contain TLA-structural characters {}();<>=
        "{ ok: true; value: t }",
        "{ ok: false; error: e }",
        // polly#144: these are REPRESENTABLE now (emitted as quoted string
        // literals + sanitized into action names), so they do NOT error —
        // they are simply unreachable here because the {...} types above
        // trigger the throw first.
        "123invalid",
        "has-dash",
        "has.dot",
        "has:colon",
      ],
      fields: [],
      handlers: [],
    };

    const generator = new TLAGenerator();

    // Should throw for the unrepresentable {...} message types.
    await expect(async () => {
      await generator.generate(mockConfig, analysis);
    }).toThrow(/Unrepresentable message type/);
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
        // Unrepresentable: no letter to seed an action name. The empty string
        // is first in iteration order, so it triggers the throw.
        "",
        " ",
        "123",
        // polly#144: everything below IS representable now (a letter plus no
        // {}();<>=), so it would NOT error on its own — only the no-letter
        // entries above do. Kept here to document the relaxed contract.
        "!invalid",
        "in valid",
        "in-valid",
        "in.valid",
        "in:valid",
        "in,valid",
        "in[valid",
        "in]valid",
      ],
      fields: [],
      handlers: [],
    };

    const generator = new TLAGenerator();

    // Should throw for the no-letter (unrepresentable) message types.
    await expect(async () => {
      await generator.generate(mockConfig, analysis);
    }).toThrow(/Unrepresentable message type/);
  });

  test("should validate TLA+ identifier in messageTypeToActionName", async () => {
    const generator = new TLAGenerator();

    // Access the private method via type assertion for testing
    const messageTypeToActionName = (generator as unknown as any).messageTypeToActionName.bind(
      generator
    );

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
