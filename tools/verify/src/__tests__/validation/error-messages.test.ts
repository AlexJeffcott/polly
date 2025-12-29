// Error Message Tests - validates error messages are clear, actionable, and helpful
// 20 comprehensive tests for validation error quality

import { describe, test, expect } from "bun:test";
import { TLAGenerator } from "../../codegen/tla";
import { TLAValidator } from "../../codegen/tla-validator";
import { SANYRunner } from "../../runner/sany";
import { RoundTripValidator } from "../../codegen/round-trip";
import { DockerRunner } from "../../runner/docker";
import type { VerificationConfig, CodebaseAnalysis } from "../../types";

describe("Error Message Quality", () => {
	const validator = new TLAValidator();
	const dockerRunner = new DockerRunner();
	const sanyRunner = new SANYRunner(dockerRunner);
	const roundTripValidator = new RoundTripValidator();

	// Helper to create config
	const createConfig = (state: Record<string, any>): VerificationConfig => ({
		state,
		messages: { maxInFlight: 3, maxTabs: 1 },
		onBuild: "warn" as const,
		onRelease: "error" as const,
	});

	// Helper to create analysis
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
	// IDENTIFIER ERROR MESSAGES (5 tests)
	// ============================================================================

	describe("Identifier Error Messages", () => {
		test("provides clear message for invalid character", () => {
			const error = validator.validateIdentifier("user-id");

			expect(error).not.toBeNull();
			expect(error?.message).toContain("user-id");
			expect(error?.message.toLowerCase()).toContain("invalid");
			expect(error?.message.length).toBeGreaterThan(20); // Descriptive
		});

		test("includes valid pattern in error message", () => {
			const error = validator.validateIdentifier("123invalid");

			expect(error).not.toBeNull();
			expect(error?.message).toContain("letter");
			expect(error?.message).toContain("letter");
			expect(error?.message).toContain("digit");
			expect(error?.message).toContain("underscore");
		});

		test("provides actionable suggestion for fix", () => {
			const error = validator.validateIdentifier("user-id");

			expect(error).not.toBeNull();
			expect(error?.suggestion).toBeDefined();
			expect(error?.suggestion).toContain("user_id");
			expect(error?.suggestion).toMatch(/try/i);
		});

		test("explains reserved word conflicts clearly", () => {
			const error = validator.validateIdentifier("TRUE");

			expect(error).not.toBeNull();
			expect(error?.type).toBe("reserved");
			expect(error?.message).toContain("TRUE");
			expect(error?.message).toContain("reserved");
			expect(error?.suggestion).toBeDefined();
		});

		test("provides helpful suggestion for reserved words", () => {
			const error = validator.validateIdentifier("IF");

			expect(error).not.toBeNull();
			expect(error?.suggestion).toBeDefined();
			expect(error?.suggestion?.length).toBeGreaterThan(10);
		});
	});

	// ============================================================================
	// BRACKET ERROR MESSAGES (5 tests)
	// ============================================================================

	describe("Bracket Error Messages", () => {
		test("indicates exact position of unmatched bracket", () => {
			const error = validator.validateBrackets("(a + b");

			expect(error).not.toBeNull();
			expect(error?.message).toContain("(");
			expect(error?.message).toMatch(/position \d+/);
		});

		test("suggests correct closing bracket", () => {
			const error = validator.validateBrackets("[unclosed");

			expect(error).not.toBeNull();
			expect(error?.suggestion).toBeDefined();
			expect(error?.suggestion).toContain("]");
		});

		test("explains mismatch clearly", () => {
			const error = validator.validateBrackets("[a + b)");

			expect(error).not.toBeNull();
			expect(error?.message).toContain("Unmatched");
			expect(error?.message).toContain(")");
		});

		test("provides context for nested brackets", () => {
			const error = validator.validateBrackets("[[a + b]");

			expect(error).not.toBeNull();
			expect(error?.message).toContain("Unclosed");
			expect(error?.suggestion).toContain("]");
		});

		test("indicates position for both opening and closing", () => {
			const error = validator.validateBrackets("(a + [b + c)");

			expect(error).not.toBeNull();
			expect(error?.message).toMatch(/position/i);
		});
	});

	// ============================================================================
	// OPERATOR ERROR MESSAGES (5 tests)
	// ============================================================================

	describe("Operator Error Messages", () => {
		test("clearly identifies invalid operator", () => {
			const error = validator.validateExpression("x === 0");

			expect(error).not.toBeNull();
			expect(error?.message).toContain("===");
			expect(error?.message.toLowerCase()).toContain("invalid");
		});

		test("provides correct TLA+ replacement", () => {
			const error = validator.validateExpression("a && b");

			expect(error).not.toBeNull();
			expect(error?.suggestion).toBeDefined();
			expect(error?.suggestion).toContain("/\\");
			expect(error?.suggestion).toContain("instead");
		});

		test("explains context restrictions clearly", () => {
			const error = validator.validateOperator("'", "invariant");

			expect(error).not.toBeNull();
			expect(error?.message.toLowerCase()).toContain("prime");
			expect(error?.message.toLowerCase()).toContain("invariant");
			expect(error?.message.toLowerCase()).toContain("action");
		});

		test("suggests moving to correct context", () => {
			const error = validator.validateOperator("[]", "action");

			expect(error).not.toBeNull();
			expect(error?.suggestion).toBeDefined();
			expect(error?.suggestion?.toLowerCase()).toContain("temporal");
		});

		test("lists all invalid JavaScript operators clearly", () => {
			const errors = [
				validator.validateExpression("x === 0"),
				validator.validateExpression("x !== 0"),
				validator.validateExpression("a && b"),
				validator.validateExpression("a || b"),
			];

			expect(errors.every((e) => e !== null)).toBe(true);
			expect(errors.every((e) => e?.message.length! > 10)).toBe(true);
		});
	});

	// ============================================================================
	// MODULE STRUCTURE ERROR MESSAGES (3 tests)
	// ============================================================================

	describe("Module Structure Error Messages", () => {
		test("explains missing MODULE declaration", () => {
			const spec = "VARIABLE x";
			const errors = validator.validateModuleStructure(spec);

			expect(errors.length).toBeGreaterThan(0);
			const moduleError = errors.find((e) => e.type === "module");
			expect(moduleError).toBeDefined();
			expect(moduleError?.message).toContain("MODULE");
			expect(moduleError?.suggestion).toBeDefined();
		});

		test("explains missing separator line", () => {
			const spec = "MODULE Test\nVARIABLE x";
			const errors = validator.validateModuleStructure(spec);

			const separatorError = errors.find((e) => e.message.includes("===="));
			expect(separatorError).toBeDefined();
			expect(separatorError?.suggestion).toBeDefined();
		});

		test("explains missing EXTENDS clause", () => {
			const spec = "MODULE Test\n====\nVARIABLE x";
			const errors = validator.validateModuleStructure(spec);

			const extendsError = errors.find((e) => e.message.includes("EXTENDS"));
			expect(extendsError).toBeDefined();
			expect(extendsError?.suggestion).toBeDefined();
		});
	});

	// ============================================================================
	// INTEGRATED ERROR MESSAGES (2 tests)
	// ============================================================================

	describe("Integrated Error Messages", () => {
		test("TLAValidationError provides comprehensive summary", async () => {
			const config = createConfig({ "invalid-field": { type: "enum", values: ["0"] } });
			const analysis = createAnalysis([], []);

			try {
				const generator = new TLAGenerator({
					validator,
					sanyRunner,
					roundTripValidator,
				});

				await generator.generate(config, analysis);
				// Should throw
				expect(true).toBe(false);
			} catch (error) {
				// Pre-validation should catch invalid field name before generation
				expect(error).toBeInstanceOf(Error);
				expect((error as Error).message).toContain("invalid-field");
			}
		});

		test("error message includes all validation layers", async () => {
			const config = createConfig({ count: { type: "enum", values: ["0"] } });
			const analysis = createAnalysis(
				["query", "missing"],
				[
					{ messageType: "query" },
					{ messageType: "missing" },
				]
			);

			// Mock a spec that will fail validation
			// We'll test this indirectly through the validators

			const roundTripResult = await roundTripValidator.validate(
				config,
				analysis,
				`
UserMessageTypes == {"query"}
State == [contextStates: [ctx |-> [count: 0]]]
`
			);

			expect(roundTripResult.valid).toBe(false);
			expect(roundTripResult.errors.length).toBeGreaterThan(0);

			// Check error message quality
			for (const error of roundTripResult.errors) {
				expect(error.message).toBeDefined();
				expect(error.message.length).toBeGreaterThan(10);
				expect(error.component).toBeDefined();
				expect(error.type).toBeDefined();
			}
		});
	});
});
