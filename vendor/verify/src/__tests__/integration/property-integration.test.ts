// Integration tests for invariants and temporal properties

import { describe, test, expect } from "bun:test";
import { TLAGenerator } from "../../codegen/tla";
import type { VerificationConfig, CodebaseAnalysis } from "../../types";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";

describe("Property Integration", () => {
	const tempDirs: string[] = [];

	const createTempProject = (files: Record<string, string>): string => {
		const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-integration-test-"));
		tempDirs.push(tempDir);

		// Create tsconfig.json
		fs.writeFileSync(
			path.join(tempDir, "tsconfig.json"),
			JSON.stringify({
				compilerOptions: {
					target: "ES2020",
					module: "commonjs",
					strict: true,
				},
			})
		);

		// Create source files
		for (const [filename, content] of Object.entries(files)) {
			fs.writeFileSync(path.join(tempDir, filename), content);
		}

		return tempDir;
	};

	process.on("exit", () => {
		for (const dir of tempDirs) {
			if (fs.existsSync(dir)) {
				fs.rmSync(dir, { recursive: true, force: true });
			}
		}
	});

	const baseConfig: VerificationConfig = {
		state: {
			count: { type: "enum", values: ["0", "1", "2"] },
		},
		messages: {
			maxInFlight: 3,
			maxTabs: 1,
		},
	};

	const baseAnalysis: CodebaseAnalysis = {
		messageTypes: ["increment", "reset"],
		handlers: [
			{
				messageType: "increment",
				node: "test",
				assignments: [
					{
						field: "count",
						value: "1",
					},
				],
				preconditions: [],
				postconditions: [],
			},
		],
		fields: [{ name: "count", type: "number" }],
		typeDefinitions: [],
	};

	// ============================================================================
	// Invariant Integration Tests
	// ============================================================================

	test("generates spec without invariants when disabled", async () => {
		const generator = new TLAGenerator();

		const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

		expect(spec).toContain("UserStateTypeInvariant");
		expect(spec).not.toContain("Extracted invariants from code annotations");
		expect(cfg).not.toContain("CountMinValue");
	});

	test("extracts and includes invariants when enabled", async () => {
		const projectPath = createTempProject({
			"handlers.ts": `
/**
 * @invariant state.count >= 0
 */
export function increment(state: any) {
  state.count++;
}
`,
		});

		const generator = new TLAGenerator({
			enableInvariants: true,
			projectPath,
		});

		const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

		// Spec should contain extracted invariant section
		expect(spec).toContain("Extracted invariants from code annotations");
		expect(spec).toContain("CountMinValue");
		expect(spec).toContain("\\A ctx \\in Contexts");

		// Config should list the invariant
		expect(cfg).toContain("INVARIANTS");
		expect(cfg).toContain("CountMinValue");
	});

	test("handles multiple invariants", async () => {
		const projectPath = createTempProject({
			"handlers.ts": `
/**
 * @invariant state.count >= 0
 * @invariant state.count <= 100
 */
export function increment(state: any) {
  state.count++;
}
`,
		});

		const generator = new TLAGenerator({
			enableInvariants: true,
			projectPath,
		});

		const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

		expect(spec).toContain("CountMinValue");
		expect(spec).toContain("CountMaxValue");
		expect(cfg).toContain("CountMinValue");
		expect(cfg).toContain("CountMaxValue");
	});

	test("translates invariant expressions to TLA+", async () => {
		const projectPath = createTempProject({
			"handlers.ts": `
/**
 * Range constraint
 * @invariant state.count >= 0 && state.count <= 100
 */
export function test() {}
`,
		});

		const generator = new TLAGenerator({
			enableInvariants: true,
			projectPath,
		});

		const { spec } = await generator.generate(baseConfig, baseAnalysis);

		// Should translate && to /\ in the invariant expression
		expect(spec).toContain("/\\");
		// The invariant definition line should have TLA+ operators
		expect(spec).toMatch(/CountMaxValue ==[\s\S]*?\/\\/);
		// The actual invariant expression should use TLA+ operators
		expect(spec).toContain("contextStates[ctx].count");
	});

	// ============================================================================
	// Temporal Property Integration Tests
	// ============================================================================

	test("generates spec without temporal properties when disabled", async () => {
		const generator = new TLAGenerator();

		const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

		expect(spec).not.toContain("Temporal Properties");
		expect(spec).not.toContain("VARIABLE delivered");
		expect(cfg).not.toContain("PROPERTIES");
	});

	test("generates temporal properties when enabled", async () => {
		const analysisWithPatterns: CodebaseAnalysis = {
			messageTypes: ["init", "request", "response"],
			handlers: [],
			fields: [],
			typeDefinitions: [],
		};

		const generator = new TLAGenerator({
			enableTemporalProperties: true,
		});

		const { spec, cfg } = await generator.generate(baseConfig, analysisWithPatterns);

		// Should have temporal properties section
		expect(spec).toContain("Temporal Properties");

		// Should have delivered tracking
		expect(spec).toContain("VARIABLE delivered");
		expect(spec).toContain("InitDelivered");
		expect(spec).toContain("MarkDelivered");

		// Should have init-first property
		expect(spec).toContain("InitMessageFirst");

		// Should have request-response property
		expect(spec).toContain("EventuallyGets");

		// Config should list properties
		expect(cfg).toContain("PROPERTIES");
	});

	test("generates multiple temporal properties", async () => {
		const analysisWithMultiplePatterns: CodebaseAnalysis = {
			messageTypes: ["init", "request", "response", "query", "result", "start", "complete"],
			handlers: [],
			fields: [],
			typeDefinitions: [],
		};

		const generator = new TLAGenerator({
			enableTemporalProperties: true,
		});

		const { spec, cfg } = await generator.generate(baseConfig, analysisWithMultiplePatterns);

		// Should detect multiple patterns
		expect(spec).toContain("RequestEventuallyGetsResponse");
		expect(spec).toContain("QueryEventuallyGetsResult");
		expect(spec).toContain("EventuallyCompletes");

		// Config should list all properties
		const propCount = (cfg.match(/PROPERTIES/g) || []).length;
		expect(propCount).toBeGreaterThanOrEqual(1);
	});

	test("generates ordering properties from handler preconditions", async () => {
		const analysisWithAuth: CodebaseAnalysis = {
			messageTypes: ["login", "updateProfile"],
			handlers: [
				{
					messageType: "updateProfile",
					node: "test",
					preconditions: [
						{
							expression: "state.authenticated === true",
							location: { line: 1, column: 1 },
						},
					],
					assignments: [],
					postconditions: [],
				},
			],
			fields: [],
			typeDefinitions: [],
		};

		const generator = new TLAGenerator({
			enableTemporalProperties: true,
		});

		const { spec } = await generator.generate(baseConfig, analysisWithAuth);

		expect(spec).toContain("RequiresLogin");
	});

	// ============================================================================
	// Combined Integration Tests
	// ============================================================================

	test("generates both invariants and temporal properties", async () => {
		const projectPath = createTempProject({
			"handlers.ts": `
/**
 * @invariant state.count >= 0
 */
export function increment(state: any) {
  state.count++;
}
`,
		});

		const analysisWithPatterns: CodebaseAnalysis = {
			messageTypes: ["init", "increment"],
			handlers: [],
			fields: [],
			typeDefinitions: [],
		};

		const generator = new TLAGenerator({
			enableInvariants: true,
			enableTemporalProperties: true,
			projectPath,
		});

		const { spec, cfg } = await generator.generate(baseConfig, analysisWithPatterns);

		// Should have both sections
		expect(spec).toContain("Extracted invariants from code annotations");
		expect(spec).toContain("Temporal Properties");

		// Should have delivered tracking
		expect(spec).toContain("VARIABLE delivered");

		// Config should have both INVARIANTS and PROPERTIES
		expect(cfg).toContain("INVARIANTS");
		expect(cfg).toContain("CountMinValue");
		expect(cfg).toContain("PROPERTIES");
		expect(cfg).toContain("InitMessageFirst");
	});

	test("maintains backward compatibility when features disabled", async () => {
		const generator = new TLAGenerator();

		const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

		// Should still generate valid TLA+
		expect(spec).toContain("MODULE UserApp");
		expect(spec).toContain("EXTENDS MessageRouter");
		expect(spec).toContain("UserStateTypeInvariant");

		// Config should be standard format
		expect(cfg).toContain("SPECIFICATION UserSpec");
		expect(cfg).toContain("INVARIANTS");
		expect(cfg).toContain("TypeOK");
	});
});
