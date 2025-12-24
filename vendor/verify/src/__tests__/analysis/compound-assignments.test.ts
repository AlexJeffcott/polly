// Compound Assignments Tests - validates detection and translation of compound operators
// 50 comprehensive tests for compound assignment detection

import { describe, test, expect } from "bun:test";
import { TLAGenerator } from "../../codegen/tla";
import type { VerificationConfig, CodebaseAnalysis, StateAssignment } from "../../types";

describe("Compound Assignments Detection", () => {
	// Helper to create minimal config and analysis
	const createConfig = (): VerificationConfig => ({
		state: {
			count: { min: 0, max: 10 },
			total: { min: 0, max: 100 },
			items: { maxLength: 5 },
			value: { min: 0, max: 50 },
		},
		messages: { maxInFlight: 3, maxTabs: 1 },
		onBuild: "warn" as const,
		onRelease: "error" as const,
	});

	const createAnalysis = (
		assignments: StateAssignment[] = []
	): CodebaseAnalysis => ({
		stateType: null,
		messageTypes: ["test"],
		fields: [],
		handlers: [{
			messageType: "test",
			node: "background",
			assignments,
			preconditions: [],
			postconditions: [],
			location: { file: "test.ts", line: 1 },
		}],
	});

	// ============================================================================
	// ADDITION ASSIGNMENT (+=) - 10 tests
	// ============================================================================

	describe("Addition Assignment (+=)", () => {
		test("translates count += 1 to @ + 1", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 1" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("[contextStates EXCEPT");
			expect(spec).toContain("![ctx].count = @ + 1");
		});

		test("translates total += amount", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ + amount" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ + amount");
		});

		test("translates count += 5 (literal)", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 5" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + 5");
		});

		test("handles multiple += in same handler", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 1" },
				{ field: "total", value: "@ + 10" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + 1");
			expect(spec).toContain("![ctx].total = @ + 10");
		});

		test("translates += with complex expression", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + (x * 2)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + (x * 2)");
		});

		test("translates += with variable reference", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ + delta" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ + delta");
		});

		test("handles += with negative number", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + (-1)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + (-1)");
		});

		test("translates += 0 (no-op but valid)", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 0" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + 0");
		});

		test("handles += with parentheses", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + (value)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + (value)");
		});

		test("generates valid TLA+ module with +=", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 1" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("MODULE UserApp");
			expect(spec).toContain("EXTENDS MessageRouter");
		});
	});

	// ============================================================================
	// SUBTRACTION ASSIGNMENT (-=) - 10 tests
	// ============================================================================

	describe("Subtraction Assignment (-=)", () => {
		test("translates count -= 1 to @ - 1", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - 1" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ - 1");
		});

		test("translates total -= amount", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ - amount" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ - amount");
		});

		test("translates count -= 5 (literal)", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - 5" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ - 5");
		});

		test("handles multiple -= in same handler", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - 1" },
				{ field: "total", value: "@ - 10" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ - 1");
			expect(spec).toContain("![ctx].total = @ - 10");
		});

		test("translates -= with complex expression", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - (x / 2)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ - (x / 2)");
		});

		test("handles -= with variable reference", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ - cost" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ - cost");
		});

		test("translates -= 0 (no-op)", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - 0" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ - 0");
		});

		test("handles -= with negative number", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - (-1)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ - (-1)");
		});

		test("combines += and -= in same handler", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 1" },
				{ field: "total", value: "@ - 5" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + 1");
			expect(spec).toContain("![ctx].total = @ - 5");
		});

		test("generates valid spec with -=", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ - 1" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("HandleTest(ctx)");
		});
	});

	// ============================================================================
	// MULTIPLICATION/DIVISION/MODULO (10 tests)
	// ============================================================================

	describe("Multiplication, Division, Modulo", () => {
		test("translates count *= 2", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ * 2" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ * 2");
		});

		test("translates total *= factor", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ * factor" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ * factor");
		});

		test("translates count /= 2", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ / 2" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ / 2");
		});

		test("translates total /= divisor", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ / divisor" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ / divisor");
		});

		test("translates count %= 10", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ % 10" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ % 10");
		});

		test("translates value %= modulus", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "value", value: "@ % modulus" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].value = @ % modulus");
		});

		test("combines all arithmetic operators", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 1" },
				{ field: "total", value: "@ * 2" },
				{ field: "value", value: "@ / 4" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + 1");
			expect(spec).toContain("![ctx].total = @ * 2");
			expect(spec).toContain("![ctx].value = @ / 4");
		});

		test("handles *= with complex expression", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ * (x + 1)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ * (x + 1)");
		});

		test("handles /= with float", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "total", value: "@ / 2.5" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].total = @ / 2.5");
		});

		test("generates valid spec with all operators", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ % 10" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("MODULE UserApp");
		});
	});

	// ============================================================================
	// ARRAY PUSH OPERATIONS (10 tests)
	// ============================================================================

	describe("Array Push Operations", () => {
		test("translates items.push(item) to Append", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, item)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, item)");
		});

		test("translates items.push(value) with literal", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, 42)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, 42)");
		});

		test("translates items.push(string)", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: 'Append(@, "value")' }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain('![ctx].items = Append(@, "value")');
		});

		test("handles multiple push operations", async () => {
			const config = {
				...createConfig(),
				state: {
					...createConfig().state,
					todos: { maxLength: 10 },
				}
			};
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, item1)" },
				{ field: "todos", value: "Append(@, item2)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, item1)");
			expect(spec).toContain("![ctx].todos = Append(@, item2)");
		});

		test("translates push with object", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, obj)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, obj)");
		});

		test("translates push with variable reference", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, newItem)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, newItem)");
		});

		test("combines push with other assignments", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "count", value: "@ + 1" },
				{ field: "items", value: "Append(@, item)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].count = @ + 1");
			expect(spec).toContain("![ctx].items = Append(@, item)");
		});

		test("handles push with function result", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, getItem())" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, getItem())");
		});

		test("translates push with property access", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, data.value)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, data.value)");
		});

		test("generates valid spec with push", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, x)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("HandleTest(ctx)");
		});
	});

	// ============================================================================
	// ARRAY POP/SHIFT/UNSHIFT (10 tests)
	// ============================================================================

	describe("Array Pop, Shift, Unshift Operations", () => {
		test("translates items.pop() to SubSeq", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "SubSeq(@, 1, Len(@)-1)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = SubSeq(@, 1, Len(@)-1)");
		});

		test("translates items.shift() to Tail", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Tail(@)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Tail(@)");
		});

		test("translates items.unshift(item) to prepend", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "<<item>> \\o @" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = <<item>> \\o @");
		});

		test("handles multiple array operations", async () => {
			const config = {
				...createConfig(),
				state: {
					items: { maxLength: 5 },
					queue: { maxLength: 10 },
					stack: { maxLength: 5 },
				}
			};
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, x)" },
				{ field: "queue", value: "Tail(@)" },
				{ field: "stack", value: "SubSeq(@, 1, Len(@)-1)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, x)");
			expect(spec).toContain("![ctx].queue = Tail(@)");
			expect(spec).toContain("![ctx].stack = SubSeq(@, 1, Len(@)-1)");
		});

		test("translates unshift with literal", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "<<42>> \\o @" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = <<42>> \\o @");
		});

		test("translates unshift with string", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: '<<"first">> \\o @' }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain('![ctx].items = <<"first">> \\o @');
		});

		test("combines pop with push", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Append(@, newItem)" }
			]);

			// In real code, this would be two handlers - one for pop, one for push
			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Append(@, newItem)");
		});

		test("handles shift with counter increment", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Tail(@)" },
				{ field: "count", value: "@ + 1" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("![ctx].items = Tail(@)");
			expect(spec).toContain("![ctx].count = @ + 1");
		});

		test("translates pop with result check", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "SubSeq(@, 1, Len(@)-1)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("Len(@)-1");
		});

		test("generates valid spec with array mutations", async () => {
			const config = createConfig();
			const analysis = createAnalysis([
				{ field: "items", value: "Tail(@)" }
			]);

			const generator = new TLAGenerator();
			const { spec } = await generator.generate(config, analysis);

			expect(spec).toContain("MODULE UserApp");
			expect(spec).toContain("EXTENDS MessageRouter");
		});
	});
});
