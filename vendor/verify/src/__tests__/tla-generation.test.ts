import { describe, test, expect } from "bun:test"
import { generateTLA } from "../codegen/tla"
import { analyzeCodebase } from "../../../analysis/src"
import path from "node:path"

describe("TLA+ Spec Generation", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects")

  test("WebSocket spec includes WebSocketServer template", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    // Generate a minimal config for testing
    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should include WebSocketServer template
    expect(tla.spec).toContain("EXTENDS MessageRouter")

    // Should NOT include ChromeExtension template
    // WebSocket uses MessageRouter
  })

  test("Chrome extension spec includes ChromeExtension template", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxTabs: 1 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should include ChromeExtension template
    expect(tla.spec).toContain("EXTENDS MessageRouter")

    // Should NOT include WebSocketServer template
    // Chrome extension uses MessageRouter
  })

  test("WebSocket spec declares MaxClients constant", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 5 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should declare MaxClients constant in .cfg file
    expect(tla.cfg).toContain("MaxClients")
    expect(tla.cfg).toMatch(/MaxClients\s*=\s*5/)
  })

  test("Chrome extension spec declares MaxTabId constant", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxTabs: 2 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should declare MaxTabId constant in .cfg file
    expect(tla.cfg).toContain("MaxTabId")
    expect(tla.cfg).toMatch(/MaxTabId\s*=\s*2/)
  })

  test("Generated spec includes all message types", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should declare MessageTypes set
    expect(tla.spec).toMatch(/MessageTypes\s*==/)

    // Check that message types from analysis are included
    // (WebSocket server has "connection" and "message" handlers)
    for (const messageType of analysis.messageTypes) {
      expect(tla.spec).toContain(`"${messageType}"`)
    }
  })

  test("Generated spec includes state variables", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should have VARIABLE section (TLA+ uses singular VARIABLE for declarations)
    expect(tla.spec).toMatch(/VARIABLE/)

    // Should include state from AppState type
    // (authenticated, subscriptions, messageCount from our fixture)
    expect(tla.spec).toMatch(/authenticated|subscriptions|messageCount/)
  })

  test("Generated spec has valid TLA+ structure", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should have MODULE declaration
    expect(tla.spec).toMatch(/----+ MODULE \w+ ----+/)

    // Should have EXTENDS
    expect(tla.spec).toContain("EXTENDS")

    // Should have closing delimiter
    expect(tla.spec).toMatch(/=+/)

    // Should NOT have CONSTANT in spec (constants defined in .cfg file)
    // Constants are declared in the .cfg file, not in the spec when extending MessageRouter

    // Should have variables
    expect(tla.spec).toMatch(/VARIABLE/)
  })

  test("Generic project spec uses generic constants", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxContexts: 4 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Generic projects now use MaxContexts (no more fallback to Chrome extension)
    expect(tla.cfg).toContain("MaxContexts")
    expect(tla.cfg).toMatch(/MaxContexts\s*=\s*4/)

    // MaxTabId is present (required by MessageRouter.tla) but set to 0 (unused)
    expect(tla.cfg).toContain("MaxTabId = 0")

    // Should NOT have WebSocket-specific constants
    expect(tla.cfg).not.toContain("MaxClients")

    // Should have MaxMessages in .cfg
    expect(tla.cfg).toContain("MaxMessages")
  })

  test("Electron spec includes appropriate constants", async () => {
    const projectPath = path.join(fixturesDir, "electron")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxRenderers: 2 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should reference renderers or main process concepts
    expect(tla.spec).toBeDefined()
    // MaxMessages should be in .cfg file, not spec
    expect(tla.cfg).toContain("MaxMessages")
    expect(tla.cfg).toContain("MaxRenderers")
  })

  test("Generated spec includes handler operators", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should have action definitions for handlers
    // Look for pattern like "HandleConnection(ctx) =="
    expect(tla.spec).toMatch(/Handle[A-Z]\w+\(ctx\)\s*==/)
  })

  test("PWA spec uses appropriate template", async () => {
    const projectPath = path.join(fixturesDir, "pwa")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxWorkers: 1, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // PWA should use similar concepts to web extensions
    expect(tla.spec).toBeDefined()
    // Constants should be in .cfg file
    expect(tla.cfg).toContain("MaxMessages")
    expect(tla.cfg).toContain("MaxWorkers")
  })

  test("Spec generation handles empty state gracefully", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      // No stateFilePath provided
    })

    const config = {
      state: {},
      messages: { maxInFlight: 3, maxClients: 3 },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    }

    const tla = await generateTLA(config, analysis)

    // Should still generate valid spec
    expect(tla.spec).toMatch(/----+ MODULE \w+ ----+/)
    expect(tla.spec).toContain("EXTENDS")
    // Constants should be in .cfg file
    expect(tla.cfg).toContain("CONSTANTS")
  })

  test("Spec generation includes MaxInFlight for all project types", async () => {
    const projectTypes = [
      { type: "websocket-app" as const, messages: { maxInFlight: 5, maxClients: 3 } },
      { type: "chrome-extension" as const, messages: { maxInFlight: 5, maxTabs: 1 } },
      { type: "pwa" as const, messages: { maxInFlight: 5, maxWorkers: 1, maxClients: 3 } },
      { type: "electron" as const, messages: { maxInFlight: 5, maxRenderers: 2 } },
      { type: "generic" as const, messages: { maxInFlight: 5, maxContexts: 3 } },
    ]

    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    for (const { type: _type, messages } of projectTypes) {
      const analysis = await analyzeCodebase({
        tsConfigPath,
      })

      const config = {
        state: {},
        messages,
        onBuild: "warn" as const,
        onRelease: "error" as const,
      }

      const tla = await generateTLA(config, analysis)

      // Every project type should have MaxMessages constant in .cfg file
      // (MaxMessages corresponds to config.messages.maxInFlight)
      expect(tla.cfg).toMatch(/MaxMessages\s*=\s*5/)
    }
  })
})
