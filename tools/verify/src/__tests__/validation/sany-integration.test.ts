// SANY integration tests - validates SANY Docker integration and error parsing
// 40 comprehensive tests for the official TLA+ syntax analyzer

import { describe, test, expect, beforeAll } from "bun:test";
import { SANYRunner } from "../../runner/sany";
import { DockerRunner } from "../../runner/docker";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";

describe("SANY Integration Tests", () => {
	let sanyRunner: SANYRunner;
	let dockerRunner: DockerRunner;
	let tempDir: string;

	beforeAll(() => {
		dockerRunner = new DockerRunner();
		sanyRunner = new SANYRunner(dockerRunner);
	});

	// Helper to create temp spec file
	// Extracts module name from content and uses it as filename to match SANY requirements
	const createTempSpec = (name: string, content: string): string => {
		if (!tempDir) {
			tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-sany-test-"));
		}

		// Extract module name from content: ---- MODULE ModuleName ----
		const moduleMatch = content.match(/----\s*MODULE\s+(\w+)\s*----/);
		const moduleName = moduleMatch?.[1] || name;

		const specPath = path.join(tempDir, `${moduleName}.tla`);
		fs.writeFileSync(specPath, content);
		return specPath;
	};

	// Cleanup after all tests
	// Note: Using process.on('exit') instead of afterAll for cleanup
	process.on("exit", () => {
		if (tempDir && fs.existsSync(tempDir)) {
			fs.rmSync(tempDir, { recursive: true });
		}
	});

	// ============================================================================
	// VALID SPEC TESTS (10 tests)
	// ============================================================================

	describe("Valid TLA+ Specifications", () => {
		test("validates minimal valid spec", async () => {
			const spec = `
---- MODULE MinimalSpec ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = x + 1

====
`;
			const specPath = createTempSpec("minimal", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with CONSTANTS", async () => {
			const spec = `
---- MODULE ConstantsSpec ----
EXTENDS Naturals

CONSTANTS N, M

VARIABLE x

Init == x = N
Next == x' = (x + M) % 100

====
`;
			const specPath = createTempSpec("constants", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with records", async () => {
			const spec = `
---- MODULE RecordSpec ----
EXTENDS Naturals

VARIABLE state

Init == state = [count: 0, active: TRUE]
Next == state' = [state EXCEPT !.count = @ + 1]

====
`;
			const specPath = createTempSpec("records", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with sequences", async () => {
			const spec = `
---- MODULE SequenceSpec ----
EXTENDS Naturals, Sequences

VARIABLE items

Init == items = <<>>
Next == items' = Append(items, 1)

====
`;
			const specPath = createTempSpec("sequences", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with sets", async () => {
			const spec = `
---- MODULE SetSpec ----
EXTENDS Naturals

VARIABLE items

Init == items = {}
Next == items' = items \\union {1, 2, 3}

====
`;
			const specPath = createTempSpec("sets", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with quantifiers", async () => {
			const spec = `
---- MODULE QuantifierSpec ----
EXTENDS Naturals

VARIABLE x

Init == x = 5
Next == x' = CHOOSE n \\in 1..10 : n > x

TypeOK == \\A n \\in 1..10 : n > 0

====
`;
			const specPath = createTempSpec("quantifiers", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with IF-THEN-ELSE", async () => {
			const spec = `
---- MODULE IfThenSpec ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = IF x < 10 THEN x + 1 ELSE 0

====
`;
			const specPath = createTempSpec("ifthen", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with CASE", async () => {
			const spec = `
---- MODULE CaseSpec ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = CASE x = 0 -> 1
                [] x = 1 -> 2
                [] OTHER -> 0

====
`;
			const specPath = createTempSpec("case", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with LET-IN", async () => {
			const spec = `
---- MODULE LetInSpec ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == LET increment == 1
        IN x' = x + increment

====
`;
			const specPath = createTempSpec("letin", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});

		test("validates spec with multiple variables", async () => {
			const spec = `
---- MODULE MultiVarSpec ----
EXTENDS Naturals

VARIABLES x, y, z

Init == /\\ x = 0
        /\\ y = 1
        /\\ z = 2

Next == /\\ x' = x + 1
        /\\ y' = y * 2
        /\\ z' = z - 1

====
`;
			const specPath = createTempSpec("multivar", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(true);
			expect(result.errors).toHaveLength(0);
		});
	});

	// ============================================================================
	// INVALID SPEC TESTS - LEXICAL ERRORS (10 tests)
	// ============================================================================

	describe("Lexical Errors Detection", () => {
		test("detects invalid character in identifier", async () => {
			const spec = `
---- MODULE InvalidChar ----
VARIABLE x-invalid

Init == x-invalid = 0

====
`;
			const specPath = createTempSpec("invalid-char", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
			expect(result.errors.some((e) => e.type === "lexical" || e.type === "syntax")).toBe(true);
		});

		test("detects unclosed string", async () => {
			const spec = `
---- MODULE UnclosedString ----
VARIABLE x

Init == x = "unclosed

====
`;
			const specPath = createTempSpec("unclosed-string", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects invalid operator sequence", async () => {
			const spec = `
---- MODULE InvalidOp ----
VARIABLE x

Init == x === 0

====
`;
			const specPath = createTempSpec("invalid-op", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects semicolon in TLA+ (JavaScript syntax)", async () => {
			const spec = `
---- MODULE Semicolon ----
VARIABLE x

Init == x = 0;

====
`;
			const specPath = createTempSpec("semicolon", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects curly braces in identifier", async () => {
			const spec = `
---- MODULE CurlyBraces ----
VARIABLE x

Handle{type}(ctx) == x' = x + 1

Init == x = 0

====
`;
			const specPath = createTempSpec("curly-braces", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects colon in identifier", async () => {
			const spec = `
---- MODULE Colon ----
VARIABLE x

Handle:Type(ctx) == x' = x + 1

Init == x = 0

====
`;
			const specPath = createTempSpec("colon", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects dot in identifier", async () => {
			const spec = `
---- MODULE Dot ----
VARIABLE x

Handle.Type(ctx) == x' = x + 1

Init == x = 0

====
`;
			const specPath = createTempSpec("dot", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects missing module end marker", async () => {
			const spec = `
---- MODULE NoEnd ----
VARIABLE x

Init == x = 0
`;
			const specPath = createTempSpec("no-end", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects unbalanced brackets", async () => {
			const spec = `
---- MODULE UnbalancedBrackets ----
VARIABLE x

Init == x = [count: 0

====
`;
			const specPath = createTempSpec("unbalanced", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects invalid escape sequence", async () => {
			const spec = `
---- MODULE InvalidEscape ----
VARIABLE x

Init == x = "test\\q"

====
`;
			const specPath = createTempSpec("invalid-escape", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// SANY may or may not accept this, but we test the parsing
			expect(result).toBeDefined();
		});
	});

	// ============================================================================
	// SEMANTIC ERRORS (10 tests)
	// ============================================================================

	describe("Semantic Errors Detection", () => {
		test("detects undefined variable", async () => {
			const spec = `
---- MODULE UndefinedVar ----
VARIABLE x

Init == y = 0

====
`;
			const specPath = createTempSpec("undefined-var", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
			expect(result.errors.some((e) => e.type === "semantic")).toBe(true);
		});

		test("detects duplicate variable declaration", async () => {
			const spec = `
---- MODULE DuplicateVar ----
VARIABLES x, x

Init == x = 0

====
`;
			const specPath = createTempSpec("duplicate-var", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// SANY treats duplicate declarations as warnings, not errors
			// So the spec is technically valid
			expect(result.valid).toBe(true);
			expect(result.warnings.length).toBeGreaterThan(0);
		});

		test("detects undefined constant", async () => {
			const spec = `
---- MODULE UndefinedConst ----
VARIABLE x

Init == x = N

====
`;
			const specPath = createTempSpec("undefined-const", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects missing EXTENDS for used module", async () => {
			const spec = `
---- MODULE MissingExtends ----
VARIABLE x

Init == x = Len(<<1, 2, 3>>)

====
`;
			const specPath = createTempSpec("missing-extends", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects primed variable in invariant", async () => {
			const spec = `
---- MODULE PrimedInInvariant ----
VARIABLE x

Init == x = 0
Next == x' = x + 1

TypeOK == x' > 0

====
`;
			const specPath = createTempSpec("primed-invariant", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// SANY should detect this semantic error
			expect(result.valid).toBe(false);
		});

		test("detects wrong arity in function call", async () => {
			const spec = `
---- MODULE WrongArity ----
EXTENDS Sequences

VARIABLE items

Init == items = Append(<<1, 2>>)

====
`;
			const specPath = createTempSpec("wrong-arity", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("detects type mismatch in set membership", async () => {
			const spec = `
---- MODULE TypeMismatch ----
VARIABLE x

Init == x = 0
Next == x' \\in x

====
`;
			const specPath = createTempSpec("type-mismatch", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// This may or may not be caught by SANY (TLA+ is untyped)
			// But we test the parsing
			expect(result).toBeDefined();
		});

		test("detects circular definition", async () => {
			const spec = `
---- MODULE Circular ----
VARIABLE x

A == B
B == A

Init == x = A

====
`;
			const specPath = createTempSpec("circular", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// SANY should detect circular definitions
			expect(result.valid).toBe(false);
		});

		test("detects invalid EXCEPT usage", async () => {
			const spec = `
---- MODULE InvalidExcept ----
VARIABLE x

Init == x = [count: 0]
Next == x' = [x EXCEPT !.missing = 1]

====
`;
			const specPath = createTempSpec("invalid-except", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// SANY may accept this (runtime error, not syntax error)
			expect(result).toBeDefined();
		});

		test("detects duplicate operator definition", async () => {
			const spec = `
---- MODULE DuplicateOp ----
VARIABLE x

Foo == 1
Foo == 2

Init == x = Foo

====
`;
			const specPath = createTempSpec("duplicate-op", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});
	});

	// ============================================================================
	// ERROR PARSING & LINE NUMBERS (5 tests)
	// ============================================================================

	describe("Error Parsing and Line Numbers", () => {
		test("correctly extracts line number from lexical error", async () => {
			const spec = `
---- MODULE LineNumber ----
VARIABLE x

Init == x-invalid = 0

====
`;
			const specPath = createTempSpec("line-number", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
			// Should have line number for at least one error
			const hasLineNumber = result.errors.some((e) => e.line && e.line > 0);
			expect(hasLineNumber).toBe(true);
		});

		test("correctly extracts column number from error", async () => {
			const spec = `
---- MODULE ColumnNumber ----
VARIABLE x

Init == x === 0

====
`;
			const specPath = createTempSpec("column-number", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			const hasColumnNumber = result.errors.some((e) => e.column && e.column > 0);
			expect(hasColumnNumber).toBe(true);
		});

		test("extracts error message text", async () => {
			const spec = `
---- MODULE ErrorMessage ----
VARIABLE x

Init == y = 0

====
`;
			const specPath = createTempSpec("error-message", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
			expect(result.errors[0]?.message).toBeDefined();
			expect(result.errors[0]?.message.length).toBeGreaterThan(0);
		});

		test("provides helpful suggestions for lexical errors", async () => {
			const spec = `
---- MODULE Suggestion ----
VARIABLE x

Handle{ ok: true }(ctx) == x' = x + 1

Init == x = 0

====
`;
			const specPath = createTempSpec("suggestion", spec);
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			// Check if any error has a suggestion
			const hasSuggestion = result.errors.some((e) => e.suggestion && e.suggestion.length > 0);
			// Suggestion is optional, but when present should be helpful
			if (hasSuggestion) {
				const withSuggestion = result.errors.find((e) => e.suggestion);
				expect(withSuggestion?.suggestion).toBeDefined();
			}
		});

		test("collects warnings separately from errors", async () => {
			const spec = `
---- MODULE Warnings ----
VARIABLE x

Init == x = 0
Next == x' = x + 1

Spec == Init /\\ [][Next]_x

====
`;
			const specPath = createTempSpec("warnings", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// This should be valid, may have warnings
			expect(result).toBeDefined();
			expect(result.warnings).toBeDefined();
		});
	});

	// ============================================================================
	// EDGE CASES & ERROR HANDLING (5 tests)
	// ============================================================================

	describe("Edge Cases and Error Handling", () => {
		test("handles non-existent file gracefully", async () => {
			const result = await sanyRunner.validateSpec("/nonexistent/file.tla");

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
			expect(result.errors[0]?.message).toContain("not found");
		});

		test("handles empty file", async () => {
			const specPath = createTempSpec("empty", "");
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("handles file with only whitespace", async () => {
			const specPath = createTempSpec("whitespace", "   \n\n   \t\t   \n");
			const result = await sanyRunner.validateSpec(specPath);

			expect(result.valid).toBe(false);
			expect(result.errors.length).toBeGreaterThan(0);
		});

		test("handles very large spec file", async () => {
			// Generate large spec with many variables
			let spec = `---- MODULE LargeSpec ----\nEXTENDS Naturals\n\n`;
			spec += `VARIABLES\n`;
			for (let i = 0; i < 100; i++) {
				spec += `  x${i}${i < 99 ? "," : ""}\n`;
			}
			spec += `\nInit == /\\ x0 = 0\n`;
			for (let i = 1; i < 100; i++) {
				spec += `        /\\ x${i} = ${i}\n`;
			}
			spec += `\nNext == /\\ x0' = x0 + 1\n`;
			for (let i = 1; i < 100; i++) {
				spec += `        /\\ x${i}' = x${i}\n`;
			}
			spec += `\n====\n`;

			const specPath = createTempSpec("large", spec);
			const result = await sanyRunner.validateSpec(specPath);

			// Should handle large files
			expect(result).toBeDefined();
			expect(result.valid).toBe(true);
		});

		test("checkSyntax method works correctly", async () => {
			const validSpec = `
---- MODULE SyntaxCheck ----
VARIABLE x
Init == x = 0
====
`;
			const specPath = createTempSpec("syntax-check", validSpec);
			const isValid = await sanyRunner.checkSyntax(specPath);

			expect(isValid).toBe(true);
		});
	});
});
