import { describe, test, expect } from "bun:test"
import { detectProjectConfig } from "../../analysis/src"
import path from "node:path"

describe("Project Detection for Verify Command", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects")

  test("detects WebSocket server project", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const config = detectProjectConfig(projectPath)

    expect(config.type).toBe("websocket-app")
    expect(config.entryPoints).toHaveProperty("server")
    expect(config.contextMapping).toEqual({
      server: "Server",
      client: "Client",
    })
  })

  test("detects PWA project", () => {
    const projectPath = path.join(fixturesDir, "pwa")
    const config = detectProjectConfig(projectPath)

    expect(config.type).toBe("pwa")
    expect(config.entryPoints).toBeDefined()
    // PWA detection should find service worker or main entry point
    expect(Object.keys(config.entryPoints).length).toBeGreaterThan(0)
  })

  test("detects Electron project", () => {
    const projectPath = path.join(fixturesDir, "electron")
    const config = detectProjectConfig(projectPath)

    expect(config.type).toBe("electron")
    expect(config.entryPoints).toHaveProperty("main")
  })

  test("provides correct context mapping for WebSocket", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const config = detectProjectConfig(projectPath)

    expect(config.contextMapping).toBeDefined()
    expect(config.contextMapping?.server).toBe("Server")
    expect(config.contextMapping?.client).toBe("Client")
  })

  test("extracts metadata from package.json", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const config = detectProjectConfig(projectPath)

    expect(config.metadata).toBeDefined()
    expect(config.metadata?.name).toBe("test-websocket-server")
  })
})
