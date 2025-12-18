import { describe, test, expect, beforeEach, afterEach } from "bun:test";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { generateStructurizrDSL } from "../codegen/structurizr";
import type { ArchitectureAnalysis } from "../../../analysis/src/types/architecture";

describe("DSL Generation", () => {
	let tempDir: string;

	beforeEach(() => {
		tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-dsl-test-"));
	});

	afterEach(() => {
		if (fs.existsSync(tempDir)) {
			fs.rmSync(tempDir, { recursive: true });
		}
	});

	describe("Component Diagrams", () => {
		test("should generate component diagrams for 'background' context (Chrome extensions)", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test Extension",
					version: "1.0.0",
					description: "Test",
				},
				contexts: {
					background: {
						type: "background",
						entryPoint: "background.ts",
						handlers: [
							{
							node: "background",
							assignments: [],
							preconditions: [],
							postconditions: [],
							location: { file: "background.ts", line: 1 },
								messageType: "query",
							},
							{
							node: "background",
							assignments: [],
							preconditions: [],
							postconditions: [],
							location: { file: "background.ts", line: 1 },
								messageType: "command",
							},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
				messageFlows: [],
				integrations: [],
			};

			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: ["background"],
			});

			// Should include background container
			expect(dsl).toContain('background = container "Background"');

			// Should include handler components
			expect(dsl).toContain("query_handler");
			expect(dsl).toContain("Query Handler");
			expect(dsl).toContain("command_handler");
			expect(dsl).toContain("Command Handler");

			// Should include component diagram view
			expect(dsl).toContain("component extension.background");
			expect(dsl).toContain("Components_Background");
		});

		test("should generate component diagrams for 'server' context (WebSocket servers)", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test Server",
					version: "1.0.0",
				},
				contexts: {
					server: {
						entryPoint: "server.ts",
						type: "server.ts",
						handlers: [
							{
						messageType: "authenticate",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
							{
						messageType: "query",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: ["server"], // This is the key - must include "server"
			});

			// Should include server container
			expect(dsl).toContain('server = container "Server"');

			// Should include handler components
			expect(dsl).toContain("authenticate_handler");
			expect(dsl).toContain("Authenticate Handler");
			expect(dsl).toContain("query_handler");
			expect(dsl).toContain("Query Handler");

			// Should include component diagram view
			expect(dsl).toContain("component extension.server");
			expect(dsl).toContain("Components_Server");
		});

		test("should NOT generate components when context not in componentDiagramContexts", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test Server",
					version: "1.0.0",
				},
				contexts: {
					server: {
						entryPoint: "server.ts",
						type: "server.ts",
						handlers: [
							{
						messageType: "query",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			// Only include "background" in componentDiagramContexts, not "server"
			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: ["background"], // BUG: Should include "server"!
			});

			// Should include server container
			expect(dsl).toContain('server = container "Server"');

			// Should NOT include handler components (this was the bug!)
			expect(dsl).not.toContain("query_handler");

			// Should NOT include component diagram view
			expect(dsl).not.toContain("component extension.server");
		});

		test("should generate components for multiple contexts", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test App",
					version: "1.0.0",
				},
				contexts: {
					background: {
						entryPoint: "background.ts",
						type: "background.ts",
						handlers: [
							{
						messageType: "sync",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
					worker: {
						entryPoint: "worker.ts",
						type: "worker.ts",
						handlers: [
							{
						messageType: "process",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: ["background", "worker"],
			});

			// Should include both containers
			expect(dsl).toContain('background = container "Background"');
			expect(dsl).toContain('worker = container "Worker"');

			// Should include handler components from both contexts
			expect(dsl).toContain("sync_handler");
			expect(dsl).toContain("process_handler");

			// Should include component diagrams for both
			expect(dsl).toContain("component extension.background");
			expect(dsl).toContain("component extension.worker");
		});

		test("should handle empty componentDiagramContexts array", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test",
					version: "1.0.0",
				},
				contexts: {
					server: {
						entryPoint: "server.ts",
						type: "server.ts",
						handlers: [
							{
						messageType: "query",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: [], // Empty array - no components should be generated
			});

			// Should include container
			expect(dsl).toContain('server = container "Server"');

			// Should NOT include handler components
			expect(dsl).not.toContain("query_handler");

			// Should NOT include component diagram
			expect(dsl).not.toContain("component extension.server");
		});

		test("should handle context with no handlers", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test",
					version: "1.0.0",
				},
				contexts: {
					server: {
						entryPoint: "server.ts",
						type: "server.ts",
						handlers: [], // No handlers
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: ["server"],
			});

			// Should include container
			expect(dsl).toContain('server = container "Server"');

			// Should still include component diagram view (even though no components)
			expect(dsl).toContain("component extension.server");
		});
	});

	describe("Auto-detect contexts (Issue #7 fix)", () => {
		test("should auto-detect all contexts when using Object.keys()", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Test Server",
					version: "1.0.0",
				},
				contexts: {
					server: {
						entryPoint: "server.ts",
						type: "server.ts",
						handlers: [
							{
						messageType: "query",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
					worker: {
						entryPoint: "worker.ts",
						type: "worker.ts",
						handlers: [
							{
						messageType: "process",
						node: "background",
						assignments: [],
						preconditions: [],
						postconditions: [],
						location: { file: "test.ts", line: 1 },
					},
						],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			// Simulate what the CLI does: Object.keys(analysis.contexts)
			const contextTypes = Object.keys(analysis.contexts);

			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: contextTypes, // Auto-detected!
			});

			// Should include both contexts with components
			expect(dsl).toContain("query_handler");
			expect(dsl).toContain("process_handler");
			expect(dsl).toContain("component extension.server");
			expect(dsl).toContain("component extension.worker");
		});
	});

	describe("Integration with different project types", () => {
		test("Chrome extension with background context", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Chrome Extension",
					version: "1.0.0",
				},
				contexts: {
					background: {
						entryPoint: "background.ts",
						type: "background.ts",
				handlers: [],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const contexts = Object.keys(analysis.contexts);
			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: contexts,
			});

			expect(dsl).toContain("test_handler");
			expect(dsl).toContain("component extension.background");
		});

		test("WebSocket server with server context", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "WebSocket Server",
					version: "1.0.0",
				},
				contexts: {
					server: {
						entryPoint: "server.ts",
						type: "server.ts",
					handlers: [],
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const contexts = Object.keys(analysis.contexts);
			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: contexts,
			});

			expect(dsl).toContain("message_handler");
			expect(dsl).toContain("component extension.server");
		});

		test("PWA with serviceworker context", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "PWA",
					version: "1.0.0",
				},
				contexts: {
					serviceworker: {
						entryPoint: "sw.ts",
					handlers: [],
						type: "sw.ts",
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const contexts = Object.keys(analysis.contexts);
			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: contexts,
			});

			expect(dsl).toContain("fetch_handler");
			expect(dsl).toContain("component extension.serviceworker");
		});

		test("Web Worker with worker context", () => {
			const analysis: ArchitectureAnalysis = {
		projectRoot: "/test",
				system: {
					name: "Web Worker",
					version: "1.0.0",
				},
				contexts: {
					worker: {
					handlers: [],
						entryPoint: "worker.ts",
						type: "worker.ts",
						chromeAPIs: [],
						externalAPIs: [],
						dependencies: [],
					},
				},
								messageFlows: [],
				integrations: [],
			};

			const contexts = Object.keys(analysis.contexts);
			const dsl = generateStructurizrDSL(analysis, {
				includeDynamicDiagrams: true,
				includeComponentDiagrams: true,
				componentDiagramContexts: contexts,
			});

			expect(dsl).toContain("compute_handler");
			expect(dsl).toContain("component extension.worker");
		});
	});
});
