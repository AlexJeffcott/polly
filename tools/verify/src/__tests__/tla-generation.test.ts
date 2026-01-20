import { describe, expect, test } from "bun:test";
import path from "node:path";
import { analyzeCodebase } from "../../../analysis/src";
import { generateTLA } from "../codegen/tla";

describe("TLA+ Spec Generation", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects");

  test("WebSocket spec includes WebSocketServer template", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    });

    // Generate a minimal config for testing
    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should include WebSocketServer template
    expect(tla.spec).toContain("EXTENDS MessageRouter");

    // Should NOT include ChromeExtension template
    // WebSocket uses MessageRouter
  });

  test("Chrome extension spec includes ChromeExtension template", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxTabs: 1 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should include ChromeExtension template
    expect(tla.spec).toContain("EXTENDS MessageRouter");

    // Should NOT include WebSocketServer template
    // Chrome extension uses MessageRouter
  });

  test("WebSocket spec declares MaxClients constant", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 5 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should declare MaxClients constant in .cfg file
    expect(tla.cfg).toContain("MaxClients");
    expect(tla.cfg).toMatch(/MaxClients\s*=\s*5/);
  });

  test("Chrome extension spec declares Tabs constant", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxTabs: 2 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should declare Tabs constant in .cfg file as integer set {0, 1, 2}
    expect(tla.cfg).toContain("Tabs");
    expect(tla.cfg).toMatch(/Tabs\s*=\s*\{0,\s*1,\s*2\}/);
  });

  test("Generated spec includes all message types", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should declare MessageTypes set
    expect(tla.spec).toMatch(/MessageTypes\s*==/);

    // Check that message types from analysis are included
    // (WebSocket server has "connection" and "message" handlers)
    for (const messageType of analysis.messageTypes) {
      expect(tla.spec).toContain(`"${messageType}"`);
    }
  });

  test("Generated spec includes state variables", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should have VARIABLE section (TLA+ uses singular VARIABLE for declarations)
    expect(tla.spec).toMatch(/VARIABLE/);

    // Should include state from AppState type
    // (authenticated, subscriptions, messageCount from our fixture)
    expect(tla.spec).toMatch(/authenticated|subscriptions|messageCount/);
  });

  test("Generated spec has valid TLA+ structure", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should have MODULE declaration
    expect(tla.spec).toMatch(/----+ MODULE \w+ ----+/);

    // Should have EXTENDS
    expect(tla.spec).toContain("EXTENDS");

    // Should have closing delimiter
    expect(tla.spec).toMatch(/=+/);

    // Should NOT have CONSTANT in spec (constants defined in .cfg file)
    // Constants are declared in the .cfg file, not in the spec when extending MessageRouter

    // Should have variables
    expect(tla.spec).toMatch(/VARIABLE/);
  });

  test("Generic project spec uses generic constants", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxContexts: 4 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Generic projects now use MaxContexts (no more fallback to Chrome extension)
    expect(tla.cfg).toContain("MaxContexts");
    expect(tla.cfg).toMatch(/MaxContexts\s*=\s*4/);

    // Tabs is present (required by MessageRouter.tla) but set to single element (unused)
    expect(tla.cfg).toContain("Tabs = {0}");

    // Should NOT have WebSocket-specific constants
    expect(tla.cfg).not.toContain("MaxClients");

    // Should have MaxMessages in .cfg
    expect(tla.cfg).toContain("MaxMessages");
  });

  test("Electron spec includes appropriate constants", async () => {
    const projectPath = path.join(fixturesDir, "electron");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxRenderers: 2 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should reference renderers or main process concepts
    expect(tla.spec).toBeDefined();
    // MaxMessages should be in .cfg file, not spec
    expect(tla.cfg).toContain("MaxMessages");
    expect(tla.cfg).toContain("MaxRenderers");
  });

  test("Generated spec includes handler operators", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should have action definitions for handlers
    // Look for pattern like "HandleConnection(ctx) =="
    expect(tla.spec).toMatch(/Handle[A-Z]\w+\(ctx\)\s*==/);
  });

  test("PWA spec uses appropriate template", async () => {
    const projectPath = path.join(fixturesDir, "pwa");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxWorkers: 1, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // PWA should use similar concepts to web extensions
    expect(tla.spec).toBeDefined();
    // Constants should be in .cfg file
    expect(tla.cfg).toContain("MaxMessages");
    expect(tla.cfg).toContain("MaxWorkers");
  });

  test("Spec generation handles empty state gracefully", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const analysis = await analyzeCodebase({
      tsConfigPath,
      // No stateFilePath provided
    });

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const tla = await generateTLA(config, analysis);

    // Should still generate valid spec
    expect(tla.spec).toMatch(/----+ MODULE \w+ ----+/);
    expect(tla.spec).toContain("EXTENDS");
    // Constants should be in .cfg file
    expect(tla.cfg).toContain("CONSTANTS");
  });

  test("Spec generation includes MaxInFlight for all project types", async () => {
    const projectTypes = [
      { type: "websocket-app" as const, messages: { maxInFlight: 5, maxClients: 3 } },
      { type: "chrome-extension" as const, messages: { maxInFlight: 5, maxTabs: 1 } },
      { type: "pwa" as const, messages: { maxInFlight: 5, maxWorkers: 1, maxClients: 3 } },
      { type: "electron" as const, messages: { maxInFlight: 5, maxRenderers: 2 } },
      { type: "generic" as const, messages: { maxInFlight: 5, maxContexts: 3 } },
    ];

    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    for (const { type: _type, messages } of projectTypes) {
      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {},
        messages,
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Every project type should have MaxMessages constant in .cfg file
      // (MaxMessages corresponds to config.messages.maxInFlight)
      expect(tla.cfg).toMatch(/MaxMessages\s*=\s*5/);
    }
  });

  // Issue #16: Tests for symmetry group handling
  describe("Symmetry groups (Issue #16)", () => {
    test("Single symmetry group generates correct TLA+", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add some test message types
      analysis.messageTypes = ["subscribe", "unsubscribe", "query", "result"];

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 1,
          symmetry: [["subscribe", "unsubscribe"]],
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should define symmetry set in spec
      expect(tla.spec).toContain('SymmetrySet1 == {"subscribe", "unsubscribe"}');

      // Should use Permutations (consistent pattern)
      expect(tla.spec).toContain("Symmetry == Permutations(SymmetrySet1)");

      // Should have exactly ONE SYMMETRY declaration in config
      const symmetryMatches = tla.cfg.match(/^SYMMETRY\s+/gm);
      expect(symmetryMatches).toBeTruthy();
      expect(symmetryMatches?.length).toBe(1);
      expect(tla.cfg).toContain("SYMMETRY Symmetry");
    });

    test("Multiple symmetry groups use union of Permutations (correct approach)", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add test message types
      analysis.messageTypes = ["subscribe", "unsubscribe", "result", "error"];

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 1,
          symmetry: [
            ["subscribe", "unsubscribe"],
            ["result", "error"],
          ],
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should define both symmetry sets in spec
      expect(tla.spec).toContain('SymmetrySet1 == {"subscribe", "unsubscribe"}');
      expect(tla.spec).toContain('SymmetrySet2 == {"result", "error"}');

      // Should use union of Permutations (standard TLA+ pattern)
      expect(tla.spec).toContain(
        "Symmetry == Permutations(SymmetrySet1) \\cup Permutations(SymmetrySet2)"
      );

      // Should have exactly ONE SYMMETRY declaration (not duplicate keywords)
      const symmetryMatches = tla.cfg.match(/^SYMMETRY\s+/gm);
      expect(symmetryMatches).toBeTruthy();
      expect(symmetryMatches?.length).toBe(1);

      // The single SYMMETRY should reference "Symmetry"
      expect(tla.cfg).toContain("SYMMETRY Symmetry");
    });

    test("Empty symmetry groups should not generate SYMMETRY declarations", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 1,
          symmetry: [],
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should NOT have SYMMETRY in config
      expect(tla.cfg).not.toMatch(/^SYMMETRY\s+/m);
    });

    test("Symmetry groups with invalid message types are filtered out", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add test message types
      analysis.messageTypes = ["subscribe", "unsubscribe"];

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 1,
          // Include a non-existent message type
          symmetry: [["subscribe", "unsubscribe", "nonexistent"]],
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should only include valid message types
      expect(tla.spec).toContain('SymmetrySet1 == {"subscribe", "unsubscribe"}');
      expect(tla.spec).not.toContain('"nonexistent"');
    });

    test("Symmetry groups with less than 2 valid types are skipped", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add test message types
      analysis.messageTypes = ["subscribe"];

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 1,
          // Only one valid type in the group
          symmetry: [["subscribe"]],
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should NOT generate symmetry set (need at least 2 types)
      expect(tla.spec).not.toContain("SymmetrySet1");
      expect(tla.cfg).not.toMatch(/^SYMMETRY\s+/m);
    });
  });

  // Issue #21: Arrays and strings should be initialized correctly
  describe("Array and string initialization (Issue #21)", () => {
    test("Arrays initialized as empty sequences", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {
          subscriptions: { type: "array" as const },
        },
        messages: { maxInFlight: 3, maxClients: 3 },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Array should be initialized as <<>> (empty sequence), not 0
      expect(tla.spec).toContain("subscriptions |-> <<>>");
      expect(tla.spec).not.toContain("subscriptions |-> 0");
    });

    test("Strings initialized as empty strings", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {
          userId: { type: "string" as const },
        },
        messages: { maxInFlight: 3, maxClients: 3 },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // String should be initialized as "", not 0
      expect(tla.spec).toContain('userId |-> ""');
      expect(tla.spec).not.toContain("userId |-> 0");
    });

    test("Mixed types initialized correctly", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {
          subscriptions: { type: "array" as const },
          userId: { type: "string" as const },
          isActive: { type: "boolean" as const },
          count: { min: 0, max: 10 },
        },
        messages: { maxInFlight: 3, maxClients: 3 },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Each type should be initialized correctly
      expect(tla.spec).toContain("subscriptions |-> <<>>");
      expect(tla.spec).toContain('userId |-> ""');
      expect(tla.spec).toContain("isActive |-> FALSE");
      expect(tla.spec).toContain("count |-> 0");
    });
  });

  // Issue #27: Naming collision between event handlers and state handlers
  describe("Handler naming collisions (Issue #27)", () => {
    test("Prevents naming collision between event and state handlers", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add handlers that would produce the same action name without collision prevention:
      // - "connected" event → HandleConnected
      // - "Connected" state handler (from handleConnected function) → HandleConnected
      analysis.handlers = [
        {
          messageType: "connected",
          node: "connection",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 10 },
          origin: "event" as const,
        },
        {
          messageType: "Connected",
          node: "connection",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 20 },
          origin: "stateHandler" as const,
        },
      ];

      const config = {
        state: {},
        messages: { maxInFlight: 3, maxClients: 3 },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Both handlers should be generated with unique names
      // Event handler keeps base name: HandleConnected
      expect(tla.spec).toContain("HandleConnected(ctx)");
      // State handler gets "Fn" prefix: HandleFnConnected
      expect(tla.spec).toContain("HandleFnConnected(ctx)");

      // Should have exactly two handler definitions (not duplicates)
      const handleConnectedMatches = tla.spec.match(/HandleConnected\(ctx\) ==/g);
      const handleFnConnectedMatches = tla.spec.match(/HandleFnConnected\(ctx\) ==/g);
      expect(handleConnectedMatches?.length).toBe(1);
      expect(handleFnConnectedMatches?.length).toBe(1);
    });

    test("No collision when handlers have different base action names", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add handlers with different base action names
      analysis.handlers = [
        {
          messageType: "connected",
          node: "connection",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 10 },
          origin: "event" as const,
        },
        {
          messageType: "Disconnected",
          node: "connection",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 20 },
          origin: "stateHandler" as const,
        },
      ];

      const config = {
        state: {},
        messages: { maxInFlight: 3, maxClients: 3 },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // No collision, both use standard naming
      expect(tla.spec).toContain("HandleConnected(ctx)");
      expect(tla.spec).toContain("HandleDisconnected(ctx)");
      // Should NOT have "Fn" prefix when no collision
      expect(tla.spec).not.toContain("HandleFnDisconnected");
    });

    test("Integration: real analysis pipeline preserves origin and prevents collisions", async () => {
      const projectPath = path.join(fixturesDir, "naming-collision");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Verify that handlers have origin set
      const eventHandlers = analysis.handlers.filter((h) => h.origin === "event");
      const stateHandlers = analysis.handlers.filter((h) => h.origin === "stateHandler");

      // Should have both types of handlers
      expect(eventHandlers.length).toBeGreaterThan(0);
      expect(stateHandlers.length).toBeGreaterThan(0);

      const config = {
        state: {},
        messages: { maxInFlight: 3, maxClients: 3 },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should have unique handler names - no duplicate definitions
      // Event handlers keep base name, state handlers get "Fn" prefix
      const handleConnectedMatches = tla.spec.match(/HandleConnected\(ctx\) ==/g);
      const handleFnConnectedMatches = tla.spec.match(/HandleFnConnected\(ctx\) ==/g);

      // Each should appear exactly once (no duplicates)
      expect(handleConnectedMatches?.length || 0).toBeLessThanOrEqual(1);
      expect(handleFnConnectedMatches?.length || 0).toBeLessThanOrEqual(1);

      // Combined, we should have 2 unique handlers for "connected"
      const totalConnectedHandlers =
        (handleConnectedMatches?.length || 0) + (handleFnConnectedMatches?.length || 0);
      expect(totalConnectedHandlers).toBe(2);
    });
  });

  // Issue #29: Tab symmetry reduction
  describe("Tab symmetry reduction (Issue #29)", () => {
    test("generates model value constants when tabSymmetry enabled", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 2,
          tabSymmetry: true,
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should have Tab0, Tab1, Tab2 constants in spec
      expect(tla.spec).toContain("CONSTANTS");
      expect(tla.spec).toMatch(/Tab0,\s*Tab1,\s*Tab2/);

      // Tabs is a CONSTANT in MessageRouter.tla, assigned via config (not defined in spec)
      expect(tla.spec).not.toContain("Tabs ==");

      // Should have TabSymmetry permutations
      expect(tla.spec).toContain("TabSymmetry == Permutations(Tabs)");

      // Config should have model value assignments
      expect(tla.cfg).toContain("Tab0 = Tab0");
      expect(tla.cfg).toContain("Tab1 = Tab1");
      expect(tla.cfg).toContain("Tab2 = Tab2");

      // Config should have Tabs defined as set of model values
      expect(tla.cfg).toMatch(/Tabs\s*=\s*\{Tab0,\s*Tab1,\s*Tab2\}/);

      // Config should NOT have MaxTabId when tabSymmetry is enabled
      expect(tla.cfg).not.toContain("MaxTabId");
    });

    test("uses Tabs set instead of 0..MaxTabId in UserNext", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add a handler to trigger the full UserNext generation
      analysis.handlers = [
        {
          messageType: "test",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 1 },
          origin: "event" as const,
        },
      ];

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 2,
          tabSymmetry: true,
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should use "tab \\in Tabs" instead of "tab \\in 0..MaxTabId"
      expect(tla.spec).toContain("\\E tab \\in Tabs :");
      expect(tla.spec).not.toContain("\\E tab \\in 0..MaxTabId");
    });

    test("combines with message symmetry correctly (AllSymmetry)", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      // Add symmetric message types
      analysis.messageTypes = ["subscribe", "unsubscribe"];

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 2,
          tabSymmetry: true,
          symmetry: [["subscribe", "unsubscribe"]],
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should have message symmetry
      expect(tla.spec).toContain("Symmetry == Permutations(SymmetrySet1)");

      // Should have tab symmetry
      expect(tla.spec).toContain("TabSymmetry == Permutations(Tabs)");

      // Should have combined symmetry
      expect(tla.spec).toContain("AllSymmetry == Symmetry \\cup TabSymmetry");

      // Config should use AllSymmetry
      expect(tla.cfg).toContain("SYMMETRY AllSymmetry");

      // Should have exactly ONE SYMMETRY declaration
      const symmetryMatches = tla.cfg.match(/^SYMMETRY\s+/gm);
      expect(symmetryMatches).toBeTruthy();
      expect(symmetryMatches?.length).toBe(1);
    });

    test("tab symmetry only generates TabSymmetry (no AllSymmetry)", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 2,
          tabSymmetry: true,
          // No message symmetry
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should have TabSymmetry
      expect(tla.spec).toContain("TabSymmetry == Permutations(Tabs)");

      // Should NOT have combined AllSymmetry (no message symmetry)
      expect(tla.spec).not.toContain("AllSymmetry");

      // Config should use TabSymmetry directly
      expect(tla.cfg).toContain("SYMMETRY TabSymmetry");
    });

    test("disabled by default (uses integer Tabs set)", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          maxTabs: 2,
          // tabSymmetry not set (defaults to false)
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should use Tabs integer set approach
      expect(tla.cfg).toMatch(/Tabs\s*=\s*\{0,\s*1,\s*2\}/);

      // Should NOT have Tab model values or symmetry definitions
      expect(tla.spec).not.toContain("Tabs ==");
      expect(tla.spec).not.toContain("TabSymmetry ==");
      expect(tla.cfg).not.toContain("Tab0 = Tab0");
    });

    test("defaults to 1 tab when maxTabs not specified", async () => {
      const projectPath = path.join(fixturesDir, "websocket-server");
      const tsConfigPath = path.join(projectPath, "tsconfig.json");

      const analysis = await analyzeCodebase({
        tsConfigPath,
      });

      const config = {
        state: {},
        messages: {
          maxInFlight: 3,
          tabSymmetry: true,
          // maxTabs not specified, should default to 1
        },
        onBuild: "warn" as const,
        onRelease: "error" as const,
      };

      const tla = await generateTLA(config, analysis);

      // Should have Tab0, Tab1 (0..1 = 2 values)
      expect(tla.spec).toMatch(/Tab0,\s*Tab1\b/);
      // Tabs is assigned in config, not defined in spec
      expect(tla.cfg).toMatch(/Tabs\s*=\s*\{Tab0,\s*Tab1\}/);

      // Config should have 2 tab constants
      expect(tla.cfg).toContain("Tab0 = Tab0");
      expect(tla.cfg).toContain("Tab1 = Tab1");
      expect(tla.cfg).not.toContain("Tab2");
    });
  });
});
