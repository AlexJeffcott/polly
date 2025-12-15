import { describe, test, expect } from "bun:test"
import { generateConfig } from "../codegen/config"
import { detectProjectConfig } from "../../analysis/src"
import path from "node:path"

describe("Config Generation for Different Project Types", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects")

  // Mock analysis result
  const mockAnalysis = {
    stateType: {
      kind: "object" as const,
      properties: {},
    },
    messageTypes: ["message1", "message2"],
    fields: [],
    handlers: [],
  }

  test("generates WebSocket-specific config", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)

    const configContent = generateConfig(mockAnalysis, projectConfig)

    // Should include WebSocket-specific fields
    expect(configContent).toContain("maxClients")
    expect(configContent).toContain("maxMessagesPerClient")
    // Should NOT include Chrome extension fields
    expect(configContent).not.toContain("maxTabs")
    // Should include project type comment
    expect(configContent).toContain("websocket-app")
  })

  test("generates Chrome extension config (backward compatibility)", () => {
    // Test without projectConfig (legacy behavior)
    const configContent = generateConfig(mockAnalysis)

    // Should default to Chrome extension fields
    expect(configContent).toContain("maxTabs")
    expect(configContent).toContain("maxInFlight")
  })

  test("generates PWA-specific config", () => {
    const projectPath = path.join(fixturesDir, "pwa")
    const projectConfig = detectProjectConfig(projectPath)

    const configContent = generateConfig(mockAnalysis, projectConfig)

    // Should include PWA-specific fields
    expect(configContent).toContain("maxWorkers")
    expect(configContent).toContain("maxClients")
    // Should include project type comment
    expect(configContent).toContain("pwa")
  })

  test("generates Electron-specific config", () => {
    const projectPath = path.join(fixturesDir, "electron")
    const projectConfig = detectProjectConfig(projectPath)

    const configContent = generateConfig(mockAnalysis, projectConfig)

    // Should include Electron-specific fields
    expect(configContent).toContain("maxRenderers")
    // Should include project type comment
    expect(configContent).toContain("electron")
  })

  test("includes entry points in config comment", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)

    const configContent = generateConfig(mockAnalysis, projectConfig)

    // Should document entry points
    expect(configContent).toContain("Entry points:")
    expect(configContent).toContain("server")
  })

  test("generates valid TypeScript code", () => {
    const projectPath = path.join(fixturesDir, "websocket-server")
    const projectConfig = detectProjectConfig(projectPath)

    const configContent = generateConfig(mockAnalysis, projectConfig)

    // Should have proper imports
    expect(configContent).toContain("import { defineVerification }")
    // Should have export
    expect(configContent).toContain("export default defineVerification")
    // Should have proper structure
    expect(configContent).toContain("state: {")
    expect(configContent).toContain("messages: {")
  })
})
