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

	describe("Automatic Relationship Detection", () => {
		test("should detect function call relationships from handler code", () => {
			const serverContext = analysis.contexts.server;
			expect(serverContext).toBeDefined();

			// Find the query handler
			const queryHandler = serverContext.handlers.find(
				(h) => h.messageType === "query",
			);
			expect(queryHandler).toBeDefined();
			expect(queryHandler?.relationships).toBeDefined();
			expect(queryHandler?.relationships?.length).toBeGreaterThan(0);

			// Should detect call to userService.listUsers()
			const userServiceRelationship = queryHandler?.relationships?.find(
				(r) => r.to === "user_service",
			);
			expect(userServiceRelationship).toBeDefined();
			expect(userServiceRelationship?.from).toBe("query_handler");
			expect(userServiceRelationship?.description).toContain("listUsers");
			expect(userServiceRelationship?.technology).toBe("Function Call");
			expect(userServiceRelationship?.confidence).toBe("high");
			expect(userServiceRelationship?.evidence.length).toBeGreaterThan(0);
		});

		test("should detect multiple relationships from command handler", () => {
			const serverContext = analysis.contexts.server;
			const commandHandler = serverContext.handlers.find(
				(h) => h.messageType === "command",
			);

			expect(commandHandler).toBeDefined();
			expect(commandHandler?.relationships).toBeDefined();
			expect(commandHandler?.relationships?.length).toBeGreaterThan(0);

			// Should detect call to userService.executeUserCommand()
			const userServiceRelationship = commandHandler?.relationships?.find(
				(r) => r.to === "user_service",
			);
			expect(userServiceRelationship).toBeDefined();
			expect(userServiceRelationship?.description).toContain(
				"executeUserCommand",
			);
		});

		test("should detect relationships from auth handler", () => {
			const serverContext = analysis.contexts.server;
			const authHandler = serverContext.handlers.find(
				(h) => h.messageType === "auth",
			);

			expect(authHandler).toBeDefined();
			expect(authHandler?.relationships).toBeDefined();

			// Should detect call to authService.authenticate()
			const authServiceRelationship = authHandler?.relationships?.find(
				(r) => r.to === "auth_service",
			);
			expect(authServiceRelationship).toBeDefined();
			expect(authServiceRelationship?.from).toBe("auth_handler");
			expect(authServiceRelationship?.description).toContain("authenticate");
			expect(authServiceRelationship?.confidence).toBe("high");
		});

		test("should include evidence for detected relationships", () => {
			const serverContext = analysis.contexts.server;
			const queryHandler = serverContext.handlers.find(
				(h) => h.messageType === "query",
			);

			expect(queryHandler?.relationships).toBeDefined();
			const relationship = queryHandler?.relationships?.[0];

			expect(relationship?.evidence).toBeDefined();
			expect(relationship?.evidence.length).toBeGreaterThan(0);
			expect(relationship?.evidence[0]).toContain("userService");
		});

		test("should deduplicate relationships within a handler", () => {
			const serverContext = analysis.contexts.server;

			// Check that each handler has unique relationships (no duplicates)
			for (const handler of serverContext.handlers) {
				if (handler.relationships) {
					const relationshipKeys = handler.relationships.map(
						(r) => `${r.from}->${r.to}`,
					);
					const uniqueKeys = new Set(relationshipKeys);
					expect(relationshipKeys.length).toBe(uniqueKeys.size);
				}
			}
		});
	});

	describe("DSL Output with Automatic Relationships", () => {
		test("should include service components in DSL", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Should include user_service component
			expect(dsl).toContain('user_service = component "User Service"');
			expect(dsl).toContain('tags "Service" "Auto-detected"');

			// Should include auth_service component
			expect(dsl).toContain('auth_service = component "Auth Service"');
		});

		test("should include auto-detected relationships in DSL", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Should include query handler -> user_service relationship
			expect(dsl).toContain("query_handler -> user_service");
			expect(dsl).toContain('Calls listUsers()');
			expect(dsl).toContain('technology "Function Call"');

			// Should include command handler -> user_service relationship
			expect(dsl).toContain("command_handler -> user_service");
			expect(dsl).toContain('Calls executeUserCommand()');

			// Should include auth handler -> auth_service relationship
			expect(dsl).toContain("auth_handler -> auth_service");
			expect(dsl).toContain('Calls authenticate()');
		});

		test("should tag auto-detected relationships", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
			});

			// Count how many auto-detected tags exist
			const autoDetectedMatches = dsl.match(/tags "Auto-detected"/g);
			expect(autoDetectedMatches).toBeDefined();
			expect(autoDetectedMatches!.length).toBeGreaterThanOrEqual(3); // 3 relationships
		});
	});

	describe("Automatic Component Grouping", () => {
		test("should group authentication handlers automatically", () => {
			// Create mock analysis with auth handlers
			const mockAnalysis: ArchitectureAnalysis = {
				...analysis,
				contexts: {
					server: {
						...analysis.contexts.server,
						handlers: [
							{ messageType: "login", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 1 } },
							{ messageType: "logout", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 2 } },
							{ messageType: "verify", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 3 } },
							{ messageType: "register", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 4 } },
						],
					},
				},
			};

			const dsl = generateStructurizrDSL(mockAnalysis, {
				componentDiagramContexts: ["server"],
			});

			// Should create "Authentication" group
			expect(dsl).toContain('group "Authentication"');
			expect(dsl).toContain("login_handler");
			expect(dsl).toContain("logout_handler");
			expect(dsl).toContain("verify_handler");
			expect(dsl).toContain("register_handler");
		});

		test("should group entity-based handlers automatically", () => {
			// Create mock analysis with entity-based handlers
			const mockAnalysis: ArchitectureAnalysis = {
				...analysis,
				contexts: {
					server: {
						...analysis.contexts.server,
						handlers: [
							{ messageType: "user_add", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 1 } },
							{ messageType: "user_update", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 2 } },
							{ messageType: "user_remove", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 3 } },
							{ messageType: "todo_add", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 4 } },
							{ messageType: "todo_remove", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 5 } },
						],
					},
				},
			};

			const dsl = generateStructurizrDSL(mockAnalysis, {
				componentDiagramContexts: ["server"],
			});

			// Should create entity groups
			expect(dsl).toContain('group "User Management"');
			expect(dsl).toContain('group "Todo Management"');
		});

		test("should group query and command handlers automatically", () => {
			// Create mock analysis with query/command handlers
			const mockAnalysis: ArchitectureAnalysis = {
				...analysis,
				contexts: {
					server: {
						...analysis.contexts.server,
						handlers: [
							{ messageType: "get_users", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 1 } },
							{ messageType: "fetch_data", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 2 } },
							{ messageType: "query_records", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 3 } },
							{ messageType: "create_item", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 4 } },
							{ messageType: "update_record", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 5 } },
							{ messageType: "delete_entry", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 6 } },
						],
					},
				},
			};

			const dsl = generateStructurizrDSL(mockAnalysis, {
				componentDiagramContexts: ["server"],
			});

			// Should create Query and Command groups
			expect(dsl).toContain('group "Query Handlers"');
			expect(dsl).toContain('group "Command Handlers"');
		});

		test("should not group when too few components", () => {
			// Current test fixture has only 3 handlers, not enough for meaningful grouping
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: ["server"],
			});

			// Should NOT contain group markers (grouping skipped)
			const groupCount = (dsl.match(/group "/g) || []).length;
			expect(groupCount).toBe(0);
		});

		test("should skip lifecycle handlers in entity grouping", () => {
			// Create mock analysis with lifecycle handlers mixed with entity handlers
			// Need enough entity handlers to meet the grouping threshold
			const mockAnalysis: ArchitectureAnalysis = {
				...analysis,
				contexts: {
					server: {
						...analysis.contexts.server,
						handlers: [
							{ messageType: "connection", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 1 } },
							{ messageType: "message", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 2 } },
							{ messageType: "close", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 3 } },
							{ messageType: "user_add", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 4 } },
							{ messageType: "user_remove", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 5 } },
							{ messageType: "user_update", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 6 } },
							{ messageType: "todo_add", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 7 } },
							{ messageType: "todo_remove", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 8 } },
						],
					},
				},
			};

			const dsl = generateStructurizrDSL(mockAnalysis, {
				componentDiagramContexts: ["server"],
			});

			// Should create entity groups, but not group lifecycle handlers
			expect(dsl).toContain('group "User Management"');
			expect(dsl).toContain('group "Todo Management"');

			// Verify entity handlers are in User Management group
			expect(dsl).toContain("user_add_handler");
			expect(dsl).toContain("user_remove_handler");
			expect(dsl).toContain("user_update_handler");

			// Verify todo handlers are in Todo Management group
			expect(dsl).toContain("todo_add_handler");
			expect(dsl).toContain("todo_remove_handler");

			// Verify lifecycle handlers exist but are not in groups
			expect(dsl).toContain("connection_handler");
			expect(dsl).toContain("message_handler");
			expect(dsl).toContain("close_handler");

			// Count groups - should be exactly 2
			const groupCount = (dsl.match(/group "/g) || []).length;
			expect(groupCount).toBe(2);
		});
	});

	describe("Automatic Dynamic Diagram Generation", () => {
		test("should generate dynamic diagram from handler relationships", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: ["server"],
				includeDynamicDiagrams: true,
			});

			// Should include dynamic keyword
			expect(dsl).toContain("dynamic");

			// Should have Message Processing Flow diagram
			expect(dsl).toContain("Message Processing Flow");
			expect(dsl).toContain("Shows message processing flow through handlers and services");
		});

		test("should include handler-to-service flows in diagram", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: ["server"],
				includeDynamicDiagrams: true,
			});

			// Should show flows from handlers to services
			expect(dsl).toContain("query_handler -> user_service");
			expect(dsl).toContain('Calls listUsers()');

			expect(dsl).toContain("command_handler -> user_service");
			expect(dsl).toContain('Calls executeUserCommand()');

			expect(dsl).toContain("auth_handler -> auth_service");
			expect(dsl).toContain('Calls authenticate()');
		});

		test("should use correct scope for dynamic diagrams", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: ["server"],
				includeDynamicDiagrams: true,
			});

			// Should scope to the server container
			expect(dsl).toContain("dynamic extension.server");
		});

		test("should generate category-specific diagrams for larger projects", () => {
			// Create mock analysis with many handlers across categories
			const mockAnalysis: ArchitectureAnalysis = {
				...analysis,
				contexts: {
					server: {
						...analysis.contexts.server,
						handlers: [
							{ messageType: "login", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 1 }, relationships: [{ from: "login_handler", to: "auth_service", description: "Authenticates", technology: "Function Call", confidence: "high", evidence: [] }] },
							{ messageType: "logout", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 2 }, relationships: [{ from: "logout_handler", to: "auth_service", description: "Logs out", technology: "Function Call", confidence: "high", evidence: [] }] },
							{ messageType: "verify", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 3 }, relationships: [{ from: "verify_handler", to: "auth_service", description: "Verifies", technology: "Function Call", confidence: "high", evidence: [] }] },
							{ messageType: "get_user", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 4 }, relationships: [{ from: "get_user_handler", to: "user_service", description: "Gets user", technology: "Function Call", confidence: "high", evidence: [] }] },
							{ messageType: "create_user", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 5 }, relationships: [{ from: "create_user_handler", to: "user_service", description: "Creates user", technology: "Function Call", confidence: "high", evidence: [] }] },
							{ messageType: "update_user", node: "server", assignments: [], preconditions: [], postconditions: [], location: { file: "test.ts", line: 6 }, relationships: [{ from: "update_user_handler", to: "user_service", description: "Updates user", technology: "Function Call", confidence: "high", evidence: [] }] },
						],
					},
				},
			};

			const dsl = generateStructurizrDSL(mockAnalysis, {
				componentDiagramContexts: ["server"],
				includeDynamicDiagrams: true,
			});

			// Should generate separate diagrams for authentication and user management
			expect(dsl).toContain("Authentication Flow");
			expect(dsl).toContain("User Management Flow");
		});

		test("should skip dynamic diagrams when option is disabled", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: ["server"],
				includeDynamicDiagrams: false,
			});

			// Should NOT include dynamic diagrams
			expect(dsl).not.toContain("dynamic extension.server");
			expect(dsl).not.toContain("Message Processing Flow");
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

	describe("Component Groups", () => {
		test("should organize components into user-defined groups", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				groups: [
					{
						name: "Business Logic Handlers",
						components: ["query_handler", "command_handler", "auth_handler"],
					},
				],
			});

			// Verify group exists
			expect(dsl).toContain('group "Business Logic Handlers" {');

			// Verify components are inside the group (with extra indentation)

			// Verify components are inside the group
			const groupStartIndex = dsl.indexOf('group "Business Logic Handlers"');
			const groupEndIndex = dsl.indexOf("\n        connection_handler", groupStartIndex);
			const groupSection = dsl.substring(groupStartIndex, groupEndIndex);

			expect(groupSection).toContain("query_handler = component");
			expect(groupSection).toContain("command_handler = component");
			expect(groupSection).toContain("auth_handler = component");
		});

		test("should support multiple groups", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				groups: [
					{
						name: "Query Handlers",
						components: ["query_handler"],
					},
					{
						name: "Command Handlers",
						components: ["command_handler"],
					},
				],
			});

			// Verify both groups exist
			expect(dsl).toContain('group "Query Handlers" {');
			expect(dsl).toContain('group "Command Handlers" {');

			// Verify components are in correct groups
			expect(dsl).toMatch(/group "Query Handlers"[^}]*query_handler = component/s);
			expect(dsl).toMatch(/group "Command Handlers"[^}]*command_handler = component/s);
		});

		test("should render ungrouped components outside groups", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				groups: [
					{
						name: "Business Logic",
						components: ["query_handler", "command_handler"],
					},
				],
			});

			// Auth handler should be outside the group (ungrouped)
			const groupMatch = dsl.match(/group "Business Logic"[^}]*\}/s);
			expect(groupMatch).toBeTruthy();

			// Auth handler should appear after the group closes
			const groupEndIndex = dsl.indexOf('group "Business Logic"');
			const authHandlerIndex = dsl.indexOf("auth_handler = component");
			const groupCloseIndex = dsl.indexOf("}", groupEndIndex);

			expect(authHandlerIndex).toBeGreaterThan(groupCloseIndex);
		});
	});

	describe("Dynamic Diagrams", () => {
		test("should generate user-provided dynamic diagrams", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				dynamicDiagrams: [
					{
						key: "message_flow",
						scope: "extension",
						title: "Message Processing Flow",
						description: "How messages are routed and handled",
						steps: [
							{ order: 1, from: "user", to: "extension.server", description: "Sends WebSocket message" },
							{ order: 2, from: "extension.server", to: "extension.server.query_handler", description: "Routes to query handler" },
							{ order: 3, from: "extension.server.query_handler", to: "extension.server", description: "Returns query result" },
						],
					},
				],
			});

			// Verify dynamic diagram exists
			expect(dsl).toContain('dynamic extension "Message Processing Flow"');
			expect(dsl).toContain("How messages are routed and handled");

			// Verify steps are in correct order
			expect(dsl).toContain('user -> extension.server "Sends WebSocket message"');
			expect(dsl).toContain('extension.server -> extension.server.query_handler "Routes to query handler"');
			expect(dsl).toContain('extension.server.query_handler -> extension.server "Returns query result"');
		});

		test("should support multiple dynamic diagrams", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				dynamicDiagrams: [
					{
						key: "query_flow",
						scope: "extension",
						title: "Query Flow",
						description: "Query handling",
						steps: [
							{ order: 1, from: "user", to: "extension.server.query_handler", description: "Query request" },
						],
					},
					{
						key: "command_flow",
						scope: "extension",
						title: "Command Flow",
						description: "Command handling",
						steps: [
							{ order: 1, from: "user", to: "extension.server.command_handler", description: "Command request" },
						],
					},
				],
			});

			// Verify both diagrams exist
			expect(dsl).toContain('dynamic extension "Query Flow"');
			expect(dsl).toContain('dynamic extension "Command Flow"');
		});
	});

	describe("Perspectives", () => {
		test("should add architectural perspectives to components", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				perspectives: {
					query_handler: [
						{ name: "Security", description: "Read-only operations, low security risk" },
						{ name: "Performance", description: "Cached for 5 minutes" },
					],
					auth_handler: [
						{ name: "Security", description: "Critical security component, uses bcrypt" },
					],
				},
			});

			// Verify query handler perspectives
			const querySection = dsl.substring(
				dsl.indexOf("query_handler = component"),
				dsl.indexOf("command_handler = component")
			);
			expect(querySection).toContain("perspectives {");
			expect(querySection).toContain('"Security" "Read-only operations, low security risk"');
			expect(querySection).toContain('"Performance" "Cached for 5 minutes"');

			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
			// Verify auth handler perspectives exist
			expect(dsl).toContain("\"Security\" \"Critical security component, uses bcrypt\"");
		});

		test("should handle components without perspectives", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				perspectives: {
					query_handler: [
						{ name: "Security", description: "Low risk" },
					],
				},
			});

			// Query handler should have perspectives
			const querySection2 = dsl.substring(
				dsl.indexOf("query_handler = component"),
				dsl.indexOf("command_handler = component")
			);
			expect(querySection2).toContain("perspectives {");

			// Command handler should NOT have perspectives
			const commandSection = dsl.substring(
				dsl.indexOf("command_handler = component"),
				dsl.indexOf("auth_handler = component")
			);
			expect(commandSection).not.toContain("perspectives {");
		});
	});

	describe("Deployment Diagrams", () => {
		test("should generate deployment environment with single node", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				deploymentNodes: [
					{
						name: "AWS EC2",
						description: "Production server",
						technology: "Amazon EC2 t3.medium",
						tags: ["environment:Production", "Cloud"],
						containerInstances: [
							{ container: "server", instances: 2 },
						],
					},
				],
			});

			// Should have deployment environment in model
			expect(dsl).toContain('deploymentEnvironment "Production"');
			expect(dsl).toContain('deploymentNode "AWS EC2" "Production server" "Amazon EC2 t3.medium"');
			expect(dsl).toContain('containerInstance extension.server 2');
			expect(dsl).toContain('tags "Cloud"');

			// Should have deployment view
			expect(dsl).toContain('deployment extension "Production"');
		});

		test("should generate nested deployment nodes", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				deploymentNodes: [
					{
						name: "AWS",
						description: "Cloud provider",
						technology: "Amazon Web Services",
						tags: ["environment:Production"],
						children: [
							{
								name: "EC2 Instance",
								description: "Application server",
								technology: "t3.medium",
								containerInstances: [
									{ container: "server", instances: 2 },
								],
							},
						],
					},
				],
			});

			// Should have nested structure
			expect(dsl).toContain('deploymentNode "AWS"');
			expect(dsl).toContain('deploymentNode "EC2 Instance"');
			expect(dsl).toContain('containerInstance extension.server 2');
		});

		test("should handle multiple deployment environments", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				deploymentNodes: [
					{
						name: "Production Server",
						description: "Production deployment",
						technology: "AWS EC2",
						tags: ["environment:Production"],
						containerInstances: [{ container: "server" }],
					},
					{
						name: "Staging Server",
						description: "Staging deployment",
						technology: "AWS EC2",
						tags: ["environment:Staging"],
						containerInstances: [{ container: "server" }],
					},
				],
			});

			// Should have both environments
			expect(dsl).toContain('deploymentEnvironment "Production"');
			expect(dsl).toContain('deploymentEnvironment "Staging"');

			// Should have both deployment views
			expect(dsl).toContain('deployment extension "Production"');
			expect(dsl).toContain('deployment extension "Staging"');
		});

		test("should include deployment node properties", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				deploymentNodes: [
					{
						name: "Kubernetes Cluster",
						description: "Production K8s",
						technology: "Kubernetes 1.28",
						tags: ["environment:Production"],
						properties: {
							Region: "us-east-1",
							"Node Count": "3",
							"Auto-scaling": "Enabled",
						},
						containerInstances: [{ container: "server", instances: 3 }],
					},
				],
			});

			// Should have properties block
			expect(dsl).toContain("properties {");
			expect(dsl).toContain('"Region" "us-east-1"');
			expect(dsl).toContain('"Node Count" "3"');
			expect(dsl).toContain('"Auto-scaling" "Enabled"');
		});

		test("should fallback to deploying all containers when none specified", () => {
			const dsl = generateStructurizrDSL(analysis, {
				componentDiagramContexts: Object.keys(analysis.contexts),
				deploymentNodes: [
					{
						name: "Simple Server",
						description: "Basic deployment",
						tags: ["environment:Production"],
						// No containerInstances specified
					},
				],
			});

			// Should deploy all contexts as fallback
			expect(dsl).toContain("containerInstance extension.server");
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

describe("Cross-File Relationship Detection (Lingua Architecture)", () => {
	const fixturesDir = path.join(__dirname, "fixtures");
	const crossFileDir = path.join(fixturesDir, "cross-file-handlers");
	const tsConfigPath = path.join(crossFileDir, "tsconfig.json");

	let analysis: ArchitectureAnalysis;

	beforeAll(async () => {
		// Verify test project exists
		if (!fs.existsSync(tsConfigPath)) {
			throw new Error(
				`Test fixture not found: ${tsConfigPath}. Run setup first.`,
			);
		}

		// Run analysis on cross-file architecture
		const analyzer = new ArchitectureAnalyzer({
			tsConfigPath,
			projectRoot: crossFileDir,
		});

		analysis = await analyzer.analyze();

		// Debug output
		console.log("\n📊 Cross-File Analysis Results:");
		console.log(`  Contexts: ${Object.keys(analysis.contexts).join(", ")}`);
		console.log(
			`  Handlers: ${Object.values(analysis.contexts).reduce((sum, ctx) => sum + ctx.handlers.length, 0)}`,
		);
		const totalRelationships = Object.values(analysis.contexts).reduce(
			(sum, ctx) =>
				sum +
				ctx.handlers.reduce(
					(handlerSum, h) => handlerSum + (h.relationships?.length || 0),
					0,
				),
			0,
		);
		console.log(`  Total relationships detected: ${totalRelationships}`);
	});

	test("should detect handlers from router file", () => {
		const serverContext = analysis.contexts.server;
		expect(serverContext).toBeDefined();
		expect(serverContext.handlers.length).toBeGreaterThanOrEqual(2);

		const messageTypes = serverContext.handlers.map((h) => h.messageType);
		expect(messageTypes).toContain("query");
		expect(messageTypes).toContain("command");
	});

	test("should follow handler calls into separate files", () => {
		const serverContext = analysis.contexts.server;

		// Find the query handler
		const queryHandler = serverContext.handlers.find(
			(h) => h.messageType === "query",
		);

		expect(queryHandler).toBeDefined();
		expect(queryHandler?.relationships).toBeDefined();
		expect(queryHandler?.relationships?.length).toBeGreaterThan(0);

		console.log(
			`\n🔍 Query Handler Relationships: ${queryHandler?.relationships?.length || 0}`,
		);
		queryHandler?.relationships?.forEach((rel) => {
			console.log(`   ${rel.from} -> ${rel.to}: ${rel.description}`);
		});
	});

	test("should detect userService.listUsers() relationship", () => {
		const serverContext = analysis.contexts.server;
		const queryHandler = serverContext.handlers.find(
			(h) => h.messageType === "query",
		);

		// Should detect call to userService.listUsers() in handlers/query.ts
		const userServiceRel = queryHandler?.relationships?.find(
			(r) => r.to === "user_service",
		);

		expect(userServiceRel).toBeDefined();
		expect(userServiceRel?.from).toBe("query_handler");
		expect(userServiceRel?.description).toContain("listUsers");
		expect(userServiceRel?.technology).toBe("Function Call");
	});

	test("should detect db.query() relationship", () => {
		const serverContext = analysis.contexts.server;
		const queryHandler = serverContext.handlers.find(
			(h) => h.messageType === "query",
		);

		// Should detect call to db.query() in handlers/query.ts
		const dbRel = queryHandler?.relationships?.find((r) => r.to === "database");

		expect(dbRel).toBeDefined();
		expect(dbRel?.from).toBe("query_handler");
		expect(dbRel?.technology).toBe("SQL");
	});

	test("should detect repositories relationship in command handler", () => {
		const serverContext = analysis.contexts.server;
		const commandHandler = serverContext.handlers.find(
			(h) => h.messageType === "command",
		);

		console.log(
			`\n🔍 Command Handler Relationships: ${commandHandler?.relationships?.length || 0}`,
		);
		commandHandler?.relationships?.forEach((rel) => {
			console.log(`   ${rel.from} -> ${rel.to}: ${rel.description}`);
		});

		// Should detect calls to repositories.users.create/update() in handlers/command.ts
		const repositoriesRel = commandHandler?.relationships?.find(
			(r) => r.to === "repositories",
		);

		expect(repositoriesRel).toBeDefined();
		expect(repositoriesRel?.from).toBe("command_handler");
		expect(repositoriesRel?.technology).toBe("Function Call");
	});

	test("should auto-generate service components in DSL", () => {
		const dsl = generateStructurizrDSL(analysis, {
			componentDiagramContexts: Object.keys(analysis.contexts),
		});

		// Should auto-generate service components
		expect(dsl).toContain('user_service = component "User Service"');
		expect(dsl).toContain('tags "Service" "Auto-detected"');

		// Should include relationships
		expect(dsl).toContain("query_handler -> user_service");
		expect(dsl).toContain("query_handler -> database");
		expect(dsl).toContain("command_handler -> repositories");
	});

	test("should generate complete DSL with cross-file relationships", () => {
		const dsl = generateStructurizrDSL(analysis, {
			componentDiagramContexts: Object.keys(analysis.contexts),
		});

		// Write for manual inspection
		const outputPath = path.join(crossFileDir, "architecture.dsl");
		fs.writeFileSync(outputPath, dsl);

		console.log(`\n✅ Cross-file DSL written to: ${outputPath}`);

		// Verify structure
		expect(dsl).toContain("workspace");
		expect(dsl).toContain("model");
		expect(dsl).toContain("views");
		expect(dsl).toContain("component extension.server");

		// Verify handlers present
		expect(dsl).toContain("query_handler");
		expect(dsl).toContain("command_handler");

		// Verify auto-detected services
		expect(dsl).toContain("user_service");
		expect(dsl).toContain("repositories");

		// Verify relationships with auto-detected tag
		const autoDetectedMatches = dsl.match(/tags "Auto-detected"/g);
		expect(autoDetectedMatches).toBeDefined();
		expect(autoDetectedMatches!.length).toBeGreaterThan(0);

		console.log(
			`   Found ${autoDetectedMatches!.length} auto-detected relationships`,
		);
	});
});
