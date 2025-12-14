import { describe, test, expect, beforeAll } from "bun:test";
import * as fs from "node:fs";
import * as path from "node:path";
import { ArchitectureAnalyzer } from "../../../analysis/src/extract/architecture";
import { generateStructurizrDSL } from "../codegen/structurizr";
import type { ArchitectureAnalysis } from "../../../analysis/src/types/architecture";

describe("Enhanced DSL Generation - REAL Integration Tests", () => {
	const fixturesDir = path.join(__dirname, "fixtures");
	const simpleWebSocketDir = path.join(fixturesDir, "simple-websocket");
	const tsConfigPath = path.join(simpleWebSocketDir, "tsconfig.json");

	let analysis: ArchitectureAnalysis;

	beforeAll(async () => {
		// Verify test project exists
		if (!fs.existsSync(tsConfigPath)) {
			throw new Error(
				`Test fixture not found: ${tsConfigPath}. Run setup first.`,
			);
		}

		// Run REAL analysis on REAL project
		const analyzer = new ArchitectureAnalyzer({
			tsConfigPath,
			projectRoot: simpleWebSocketDir,
		});

		analysis = await analyzer.analyze();

		// Debug output
		console.log("\n📊 Analysis Results:");
		console.log(`  Contexts: ${Object.keys(analysis.contexts).join(", ")}`);
		console.log(
			`  Handlers: ${Object.values(analysis.contexts).reduce((sum, ctx) => sum + ctx.handlers.length, 0)}`,
		);
		console.log(`  Message flows: ${analysis.messageFlows.length}`);
		console.log(`  Integrations: ${analysis.integrations.length}`);
	});

	describe("Project Analysis", () => {
		test("should detect WebSocket server context", () => {
			expect(Object.keys(analysis.contexts)).toContain("server");
		});

		test("should detect business logic message handlers", () => {
			const serverContext = analysis.contexts.server;
			expect(serverContext).toBeDefined();
				// Should detect both WebSocket lifecycle handlers (connection, message, close)
			// and business logic handlers (query, command, auth)
			expect(serverContext.handlers.length).toBeGreaterThanOrEqual(3);

			const messageTypes = serverContext.handlers.map((h) => h.messageType);
			expect(messageTypes).toContain("query");
			expect(messageTypes).toContain("command");
			expect(messageTypes).toContain("auth");
		});

		test("should detect ws integration", () => {
			const wsIntegration = analysis.integrations.find(
				(i) => i.name === "ws",
			);
			expect(wsIntegration).toBeDefined();
			expect(wsIntegration?.type).toBe("external-script");
		});
	});

	describe("Default Styling", () => {
		test("should generate DSL with default styles", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Should include styles section
			expect(dsl).toContain("styles {");

			// Should include Message Handler style
			expect(dsl).toContain('element "Message Handler"');
			expect(dsl).toContain("shape Hexagon");
			expect(dsl).toContain("background #1168bd");

			// Should include Query style (green)
			expect(dsl).toContain('element "Query"');
			expect(dsl).toContain("background #51cf66");

			// Should include Command style (orange)
			expect(dsl).toContain('element "Command"');
			expect(dsl).toContain("background #ff922b");

			// Should include Authentication style (red)
			expect(dsl).toContain('element "Authentication"');
			expect(dsl).toContain("background #ff6b6b");

			// Should include Relationship style
			expect(dsl).toContain('relationship "Relationship"');
			expect(dsl).toContain("routing Orthogonal");
		});

		test("should include theme URL", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			expect(dsl).toContain(
				"theme https://static.structurizr.com/themes/default/theme.json",
			);
		});

		test("should apply handler-specific colors to components", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Query handler should have Query tag
			expect(dsl).toMatch(/query_handler.*tags.*Query/s);

			// Command handler should have Command tag
			expect(dsl).toMatch(/command_handler.*tags.*Command/s);

			// Auth handler should have Authentication tag
			expect(dsl).toMatch(/auth_handler.*tags.*Authentication/s);
		});
	});

	describe("Custom Styling", () => {
		test("should allow custom element styles", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				styles: {
					elements: {
						"Message Handler": {
							shape: "RoundedBox",
							background: "#custom",
							color: "#ffffff",
						},
					},
				},
			});

			expect(dsl).toContain('element "Message Handler"');
			expect(dsl).toContain("shape RoundedBox");
			expect(dsl).toContain("background #custom");
		});

		test("should allow disabling default styles", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				includeDefaultStyles: false,
			});

			// Should have minimal styles section
			expect(dsl).toContain("styles {");
			expect(dsl).toContain("    }");

			// Should NOT include default element styles
			expect(dsl).not.toContain('element "Message Handler"');
		});

		test("should allow custom theme URL", () => {
			const customTheme = "https://custom.theme.com/theme.json";
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				styles: {
					theme: customTheme,
				},
			});

			expect(dsl).toContain(`theme ${customTheme}`);
		});
	});

	describe("Properties & Metadata", () => {
		test("should include source file paths with line numbers", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Should include source file paths for handlers
			expect(dsl).toMatch(/properties\s*\{[^}]*"Source"\s+"[^"]+\.ts:\d+"/s);

			// Verify specific handlers have source info
			expect(dsl).toContain('src/server/handlers.ts:55'); // query handler
			expect(dsl).toContain('src/server/handlers.ts:57'); // command handler
			expect(dsl).toContain('src/server/handlers.ts:59'); // auth handler
		});

		test("should include technology stack", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Should include TypeScript and WebSocket
			expect(dsl).toMatch(/properties\s*\{[^}]*"Technology"\s+"[^"]*TypeScript[^"]*"/s);
			expect(dsl).toMatch(/properties\s*\{[^}]*"Technology"\s+"[^"]*WebSocket[^"]*"/s);
		});

		test("should include message type and pattern", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Query handler should have Query message type and Query Handler pattern
			expect(dsl).toMatch(/query_handler[^}]*properties\s*\{[^}]*"Message Type"\s+"Query"/s);
			expect(dsl).toMatch(/query_handler[^}]*properties\s*\{[^}]*"Pattern"\s+"Query Handler"/s);

			// Command handler should have Command message type and Command Handler pattern
			expect(dsl).toMatch(/command_handler[^}]*properties\s*\{[^}]*"Message Type"\s+"Command"/s);
			expect(dsl).toMatch(/command_handler[^}]*properties\s*\{[^}]*"Pattern"\s+"Command Handler"/s);

			// Auth handler should have Authentication message type and Authentication Handler pattern
			expect(dsl).toMatch(/auth_handler[^}]*properties\s*\{[^}]*"Message Type"\s+"Authentication"/s);
			expect(dsl).toMatch(/auth_handler[^}]*properties\s*\{[^}]*"Pattern"\s+"Authentication Handler"/s);
		});

		test("should allow custom properties", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				properties: {
					query: {
						"Custom Property": "Custom Value",
						"Team": "Data Team",
					},
				},
			});

			// Should include custom properties
			expect(dsl).toMatch(/query_handler[^}]*properties\s*\{[^}]*"Custom Property"\s+"Custom Value"/s);
			expect(dsl).toMatch(/query_handler[^}]*properties\s*\{[^}]*"Team"\s+"Data Team"/s);
		});
	});

	describe("Component Relationships", () => {
		test("should support explicit relationships between components", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				relationships: [
					{
						from: "query_handler",
						to: "user_service",
						description: "Calls listUsers()",
						technology: "TypeScript",
						tags: ["Sync"],
					},
					{
						from: "command_handler",
						to: "user_service",
						description: "Calls executeUserCommand()",
						technology: "TypeScript",
						tags: ["Sync"],
					},
				],
			});

			// Verify relationships are in DSL
			expect(dsl).toMatch(/query_handler\s*->\s*user_service\s+"Calls listUsers\(\)"/);
			expect(dsl).toMatch(/command_handler\s*->\s*user_service\s+"Calls executeUserCommand\(\)"/);

			// Verify technology and tags
			expect(dsl).toContain('technology "TypeScript"');
			expect(dsl).toMatch(/tags\s+"Sync"/);
		});

		test("should generate relationships without technology or tags", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				relationships: [
					{
						from: "auth_handler",
						to: "auth_service",
						description: "Authenticates user",
					},
				],
			});

			// Verify minimal relationship
			expect(dsl).toMatch(/auth_handler\s*->\s*auth_service\s+"Authenticates user"/);
		});
	});

	describe("DSL Structure", () => {
		test("should generate valid Structurizr DSL structure", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Basic structure
			expect(dsl).toContain("workspace");
			expect(dsl).toContain("model {");
			expect(dsl).toContain("views {");
			expect(dsl).toContain("styles {");

			// Should have matching braces
			const openBraces = (dsl.match(/{/g) || []).length;
			const closeBraces = (dsl.match(/}/g) || []).length;
			expect(openBraces).toBe(closeBraces);
		});

		test("should include all handler components", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			expect(dsl).toContain("query_handler");
			expect(dsl).toContain("command_handler");
			expect(dsl).toContain("auth_handler");

			// Should have component descriptions
			expect(dsl).toContain("Query Handler");
			expect(dsl).toContain("Command Handler");
			expect(dsl).toContain("Auth Handler");
		});

		test("should include component diagram for server context", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			expect(dsl).toContain("component extension.server");
			expect(dsl).toContain("Components_Server");
		});
	});

	describe("Output Validation", () => {
		test("should write valid DSL to file", () => {
			const outputPath = path.join(simpleWebSocketDir, "architecture.dsl");

			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			fs.writeFileSync(outputPath, dsl);

			expect(fs.existsSync(outputPath)).toBe(true);

			const written = fs.readFileSync(outputPath, "utf-8");
			expect(written).toBe(dsl);

			console.log(`\n✅ DSL written to: ${outputPath}`);
			console.log(`   View with: structurizr/lite docker container`);
		});
	});

	describe("Visual Verification Instructions", () => {
		test("should provide instructions for manual verification", () => {
			const outputPath = path.join(simpleWebSocketDir, "architecture.dsl");

			console.log("\n📋 Manual Verification Steps:");
			console.log("1. Run Structurizr Lite:");
			console.log(
				`   docker run -it --rm -p 8080:8080 -v ${simpleWebSocketDir}:/usr/local/structurizr structurizr/lite`,
			);
			console.log("2. Open http://localhost:8080");
			console.log("3. Verify:");
			console.log("   ✓ Query handler is GREEN (#51cf66)");
			console.log("   ✓ Command handler is ORANGE (#ff922b)");
			console.log("   ✓ Auth handler is RED (#ff6b6b)");
			console.log("   ✓ All handlers are HEXAGONS");
			console.log("   ✓ Component diagram shows all 3 handlers");
			console.log("   ✓ No rendering errors");

			// This test always passes - it's just for documentation
			expect(true).toBe(true);
		});
	});
});
