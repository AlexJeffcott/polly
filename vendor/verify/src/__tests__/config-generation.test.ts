import { describe, test, expect } from "bun:test"
import { generateConfig } from "../codegen/config"

describe("Config Generation for Different Project Types", () => {
  // Mock analysis result
  const mockAnalysis = {
    stateType: {
      name: "MockState",
      kind: "object" as const,
      nullable: false,
      properties: {},
    },
    messageTypes: ["message1", "message2"],
    fields: [],
    handlers: [],
  }

  test("generates WebSocket-specific config", () => {
    const configContent = generateConfig(mockAnalysis)

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
    const configContent = generateConfig(mockAnalysis)

    // Should include PWA-specific fields
    expect(configContent).toContain("maxWorkers")
    expect(configContent).toContain("maxClients")
    // Should include project type comment
    expect(configContent).toContain("pwa")
  })

  test("generates Electron-specific config", () => {
    const configContent = generateConfig(mockAnalysis)

    // Should include Electron-specific fields
    expect(configContent).toContain("maxRenderers")
    // Should include project type comment
    expect(configContent).toContain("electron")
  })

  test("includes entry points in config comment", () => {
    const configContent = generateConfig(mockAnalysis)

    // Should document entry points
    expect(configContent).toContain("Entry points:")
    expect(configContent).toContain("server")
  })

  test("generates valid TypeScript code", () => {
    const configContent = generateConfig(mockAnalysis)

    // Should have proper imports
    expect(configContent).toContain("import { defineVerification }")
    // Should have export
    expect(configContent).toContain("export default defineVerification")
    // Should have proper structure
    expect(configContent).toContain("state: {")
    expect(configContent).toContain("messages: {")
  })
})
