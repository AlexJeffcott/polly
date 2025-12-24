import { describe, test, expect } from "bun:test";
import { TLAGenerator } from "../tla";
import type { VerificationConfig, CodebaseAnalysis } from "../../types";

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
		const { spec } = await generator.generate(mockConfig, analysis);

		// Should contain valid handler names (in PascalCase)
		expect(spec).toContain("HandleQuery");
		expect(spec).toContain("HandleCommand");

		// Should NOT contain invalid handler names with braces, colons, semicolons
		expect(spec).not.toContain("Handle{");
		expect(spec).not.toContain("ok:");
		expect(spec).not.toContain("value:");
		expect(spec).not.toContain(";");

		// The spec should be valid TLA+ syntax (basic check)
		// Valid TLA+ function names should only contain alphanumeric and underscore
		const handlerFunctionPattern = /Handle[a-zA-Z0-9_]+\s*\(/g;
		const handlerMatches = spec.match(handlerFunctionPattern);

		if (handlerMatches) {
			for (const match of handlerMatches) {
				// Extract the function name
				const funcName = match.replace(/\s*\($/, "");
				// Should match valid TLA+ identifier pattern
				expect(funcName).toMatch(/^Handle[a-zA-Z][a-zA-Z0-9_]*$/);
			}
		}
	});

	test("should only include valid message types in UserMessageTypes set", async () => {
		const analysis: CodebaseAnalysis = {
			stateType: null,
			messageTypes: [
				"authenticate",
				"query",
				"command",
				// Invalid types (should be filtered)
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
		const { spec } = await generator.generate(mockConfig, analysis);

		// Find the UserMessageTypes definition
		const messageTypesMatch = spec.match(/UserMessageTypes\s*==\s*\{([^}]+)\}/);
		expect(messageTypesMatch).toBeTruthy();

		if (messageTypesMatch && messageTypesMatch[1]) {
			const messageTypesString = messageTypesMatch[1];

			// Should contain valid types
			expect(messageTypesString).toContain('"authenticate"');
			expect(messageTypesString).toContain('"query"');
			expect(messageTypesString).toContain('"command"');

			// Should NOT contain invalid types with special characters
			expect(messageTypesString).not.toContain("{ ok: true");
			expect(messageTypesString).not.toContain("{ ok: false");
			expect(messageTypesString).not.toContain("{");
			expect(messageTypesString).not.toContain("}");
			expect(messageTypesString).not.toContain("123invalid");
			expect(messageTypesString).not.toContain("has-dash");
			expect(messageTypesString).not.toContain("has.dot");
			expect(messageTypesString).not.toContain("has:colon");
		}
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
		const { spec } = await generator.generate(mockConfig, analysis);

		// Find the UserMessageTypes definition
		const messageTypesMatch = spec.match(/UserMessageTypes\s*==\s*\{([^}]+)\}/);
		expect(messageTypesMatch).toBeTruthy();

		if (messageTypesMatch && messageTypesMatch[1]) {
			const messageTypesString = messageTypesMatch[1];

			// Valid types should be included
			expect(messageTypesString).toContain('"a"');
			expect(messageTypesString).toContain('"A"');
			expect(messageTypesString).toContain('"message123"');
			expect(messageTypesString).toContain('"MESSAGE_TYPE"');
			expect(messageTypesString).toContain('"message_type_with_underscores"');

			// Invalid types should be filtered out
			// Note: We can't easily check for empty string, but the spec should be parseable
			// Extract all message type strings from the set
			const messageTypeMatches = messageTypesString.match(/"([^"]*)"/g);
			if (messageTypeMatches) {
				const extractedTypes = messageTypeMatches.map((m: string) => m.slice(1, -1)); // Remove quotes

				// Check that no extracted type contains invalid characters
				const invalidCharsInIdentifiers = ["!", "-", ".", ":", ";", "{", "}", "[", "]", "(", ")", " "];
				for (const type of extractedTypes) {
					for (const char of invalidCharsInIdentifiers) {
						expect(type).not.toContain(char);
					}

					// Also verify it matches the TLA+ identifier pattern
					if (type.length > 0) { // Allow empty for edge case testing
						expect(type).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
					}
				}
			}
		}

		// The generated spec should be parseable as TLA+ (basic validation)
		expect(spec).toContain("MODULE UserApp");
		expect(spec).not.toContain("Handle{");
		expect(spec).not.toContain("Handle[");
		expect(spec).not.toContain("Handle(");
		expect(spec).not.toContain("Handle!");
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
