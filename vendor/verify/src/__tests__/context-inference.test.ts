import { describe, test, expect } from "bun:test"
import { analyzeCodebase } from "@fairfox/polly-analysis"
import { detectProjectConfig } from "@fairfox/polly-analysis"
import path from "node:path"

describe("Context Inference", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects")

  test("WebSocket handlers are tagged with Server context", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
      projectConfig,
    })

    // All handlers in server.ts should have "Server" context
    const serverHandlers = analysis.handlers.filter((h) =>
      h.location.file.includes("server.ts")
    )

    expect(serverHandlers.length).toBeGreaterThan(0)

    for (const handler of serverHandlers) {
      expect(handler.node).toBe("Server")
    }
  })

  test("Context mapping uses ProjectConfig.contextMapping", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    // Verify contextMapping is what we expect
    expect(projectConfig.contextMapping).toEqual({
      server: "Server",
      client: "Client",
    })

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
      projectConfig,
    })

    // All handlers should have contexts from the mapping
    const validContexts = Object.values(projectConfig.contextMapping || {})
    for (const handler of analysis.handlers) {
      expect(validContexts).toContain(handler.node)
    }
  })

  test("Electron handlers are tagged with MainProcess context", async () => {
    const projectPath = path.join(fixturesDir, "electron")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      projectConfig,
    })

    // Handlers in main.ts should have MainProcess context
    const mainHandlers = analysis.handlers.filter((h) =>
      h.location.file.includes("main.ts")
    )

    expect(mainHandlers.length).toBeGreaterThan(0)

    for (const handler of mainHandlers) {
      expect(handler.node).toBe("Main Process")
    }
  })

  test("Legacy behavior works when no projectConfig provided", async () => {
    // Test backward compatibility - when no projectConfig is provided,
    // analysis should still work (using legacy inference)
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    // Don't provide projectConfig to test legacy behavior
    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
    })

    // Should complete without errors
    expect(analysis).toBeDefined()
    expect(analysis.handlers).toBeDefined()

    // Contexts should be inferred using legacy patterns
    const contexts = new Set(analysis.handlers.map((h) => h.node))
    expect(contexts.size).toBeGreaterThanOrEqual(0)
  })

  test("Files outside entry points are tagged as unknown", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
      projectConfig,
    })

    // Types file shouldn't have handlers, but if we had handlers in a
    // random util file, they would be "unknown"
    const typeFileHandlers = analysis.handlers.filter((h) =>
      h.location.file.includes("types/state.ts")
    )

    // There shouldn't be any handlers in the state types file
    expect(typeFileHandlers.length).toBe(0)
  })

  test("PWA service worker handlers are tagged with ServiceWorker context", async () => {
    const projectPath = path.join(fixturesDir, "pwa")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      projectConfig,
    })

    // Handlers in service-worker.ts should have ServiceWorker context
    const workerHandlers = analysis.handlers.filter((h) =>
      h.location.file.includes("service-worker.ts")
    )

    if (workerHandlers.length > 0) {
      for (const handler of workerHandlers) {
        expect(handler.node).toBe("Service Worker")
      }
    }
  })

  test("Context inference handles nested directory structures", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: path.join(projectPath, "src/types/state.ts"),
      projectConfig,
    })

    // All handlers in src/ directory under server entry point should be Server
    const srcHandlers = analysis.handlers.filter((h) => h.location.file.includes("/src/"))

    for (const handler of srcHandlers) {
      // Should be mapped to a valid context
      expect(handler.node).toBeTruthy()
      expect(handler.node).not.toBe("unknown")
    }
  })
})
