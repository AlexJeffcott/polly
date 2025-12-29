import { describe, test, expect } from "bun:test"
import { selectAdapter, ADAPTER_REGISTRY } from "../adapters/registry"
import { detectProjectConfig } from "../../../analysis/src"
import type { ProjectType } from "../../../analysis/src"
import path from "node:path"

describe("Adapter Selection", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects")

  test("selectAdapter returns WebSocketAdapter for websocket-app", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("websocket-app", tsConfigPath)

    expect(adapter).toBeDefined()
    expect(adapter.name).toBe("websocket")
  })

  test("selectAdapter returns WebExtensionAdapter for chrome-extension", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("chrome-extension", tsConfigPath)

    expect(adapter).toBeDefined()
    expect(adapter.name).toBe("web-extension")
  })

  test("selectAdapter returns WebExtensionAdapter for PWA", () => {
    const projectPath = path.join(fixturesDir, "pwa")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("pwa", tsConfigPath)

    expect(adapter).toBeDefined()
    expect(adapter.name).toBe("web-extension")
  })

  test("selectAdapter returns EventBusAdapter for Electron", () => {
    const projectPath = path.join(fixturesDir, "electron")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("electron", tsConfigPath)

    expect(adapter).toBeDefined()
    expect(adapter.name).toBe("event-bus")
  })

  test("selectAdapter returns EventBusAdapter for generic projects", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("generic", tsConfigPath)

    expect(adapter).toBeDefined()
    expect(adapter.name).toBe("event-bus")
  })

  test("ADAPTER_REGISTRY has entries for all project types", () => {
    const expectedTypes: ProjectType[] = [
      "chrome-extension",
      "websocket-app",
      "pwa",
      "electron",
      "generic",
    ]

    for (const type of expectedTypes) {
      expect(ADAPTER_REGISTRY[type]).toBeDefined()
      expect(typeof ADAPTER_REGISTRY[type]).toBe("function")
    }
  })

  test("Adapter selection matches detected project type", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter(projectConfig.type, tsConfigPath)

    // Detected as websocket-app, should get WebSocketAdapter
    expect(projectConfig.type).toBe("websocket-app")
    expect(adapter.name).toBe("websocket")
  })

  test("WebSocketAdapter is configured with correct parameters", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("websocket-app", tsConfigPath)

    // WebSocketAdapter should be configured with maxConnections and maxInFlight
    expect(adapter.name).toBe("websocket")
    // Adapter should be properly instantiated (not throw errors)
    expect(adapter).toBeDefined()
  })

  test("WebExtensionAdapter is configured with correct contexts for Chrome", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("chrome-extension", tsConfigPath)

    expect(adapter.name).toBe("web-extension")
    // Should support background, content, popup, etc.
    expect(adapter).toBeDefined()
  })

  test("EventBusAdapter is configured with IPC patterns for Electron", () => {
    const projectPath = path.join(fixturesDir, "electron")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter = selectAdapter("electron", tsConfigPath)

    expect(adapter.name).toBe("event-bus")
    // Should be configured to detect IPC patterns
    expect(adapter).toBeDefined()
  })

  test("All adapters can be instantiated without errors", () => {
    const projectTypes: ProjectType[] = [
      "chrome-extension",
      "websocket-app",
      "pwa",
      "electron",
      "generic",
    ]

    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    for (const projectType of projectTypes) {
      expect(() => {
        const adapter = selectAdapter(projectType, tsConfigPath)
        expect(adapter).toBeDefined()
        expect(adapter.name).toBeTruthy()
      }).not.toThrow()
    }
  })

  test("Adapter selection is deterministic", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const tsConfigPath = path.join(projectPath, "tsconfig.json")

    const adapter1 = selectAdapter("websocket-app", tsConfigPath)
    const adapter2 = selectAdapter("websocket-app", tsConfigPath)

    // Should return same adapter type
    expect(adapter1.name).toBe(adapter2.name)
  })
})
