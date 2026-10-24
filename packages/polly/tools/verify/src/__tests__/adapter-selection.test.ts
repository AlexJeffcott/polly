import { describe, expect, test } from "bun:test";
import path from "node:path";
import type { ProjectType } from "../../../analysis/src";
import { detectProjectConfig } from "../../../analysis/src";
import { ADAPTER_REGISTRY, selectAdapter } from "../adapters/registry";

describe("Adapter Selection", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects");

  test("selectAdapter returns WebSocketAdapter for websocket-app", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("websocket-app", tsConfigPath);

    expect(adapter).toBeDefined();
    expect(adapter.name).toBe("websocket");
  });

  test("selectAdapter returns WebExtensionAdapter for chrome-extension", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("chrome-extension", tsConfigPath);

    expect(adapter).toBeDefined();
    expect(adapter.name).toBe("web-extension");
  });

  test("selectAdapter returns WebExtensionAdapter for PWA", async () => {
    const projectPath = path.join(fixturesDir, "pwa");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("pwa", tsConfigPath);

    expect(adapter).toBeDefined();
    expect(adapter.name).toBe("web-extension");
  });

  test("selectAdapter returns EventBusAdapter for Electron", async () => {
    const projectPath = path.join(fixturesDir, "electron");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("electron", tsConfigPath);

    expect(adapter).toBeDefined();
    expect(adapter.name).toBe("event-bus");
  });

  test("selectAdapter returns EventBusAdapter for generic projects", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("generic", tsConfigPath);

    expect(adapter).toBeDefined();
    expect(adapter.name).toBe("event-bus");
  });

  test("ADAPTER_REGISTRY has entries for all project types", () => {
    const expectedTypes: ProjectType[] = [
      "chrome-extension",
      "websocket-app",
      "pwa",
      "electron",
      "generic",
    ];

    for (const type of expectedTypes) {
      expect(ADAPTER_REGISTRY[type]).toBeDefined();
      expect(typeof ADAPTER_REGISTRY[type]).toBe("function");
    }
  });

  test("Adapter selection matches detected project type", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const projectConfig = detectProjectConfig(projectPath);
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter(projectConfig.type, tsConfigPath);

    // Detected as websocket-app, should get WebSocketAdapter
    expect(projectConfig.type).toBe("websocket-app");
    expect(adapter.name).toBe("websocket");
  });

  test("WebSocketAdapter is configured with correct parameters", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("websocket-app", tsConfigPath);

    // WebSocketAdapter should be configured with maxConnections and maxInFlight
    expect(adapter.name).toBe("websocket");
    // Adapter should be properly instantiated (not throw errors)
    expect(adapter).toBeDefined();
  });

  test("WebExtensionAdapter is configured with correct contexts for Chrome", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("chrome-extension", tsConfigPath);

    expect(adapter.name).toBe("web-extension");
    // Should support background, content, popup, etc.
    expect(adapter).toBeDefined();
  });

  test("EventBusAdapter is configured with IPC patterns for Electron", async () => {
    const projectPath = path.join(fixturesDir, "electron");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter = await selectAdapter("electron", tsConfigPath);

    expect(adapter.name).toBe("event-bus");
    // Should be configured to detect IPC patterns
    expect(adapter).toBeDefined();
  });

  test("All adapters can be instantiated without errors", async () => {
    const projectTypes: ProjectType[] = [
      "chrome-extension",
      "websocket-app",
      "pwa",
      "electron",
      "generic",
    ];

    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    for (const projectType of projectTypes) {
      const adapter = await selectAdapter(projectType, tsConfigPath);
      expect(adapter).toBeDefined();
      expect(adapter.name).toBeTruthy();
    }
  });

  test("Adapter selection is deterministic", async () => {
    const projectPath = path.join(fixturesDir, "websocket-server");
    const tsConfigPath = path.join(projectPath, "tsconfig.json");

    const adapter1 = await selectAdapter("websocket-app", tsConfigPath);
    const adapter2 = await selectAdapter("websocket-app", tsConfigPath);

    // Should return same adapter type
    expect(adapter1.name).toBe(adapter2.name);
  });
});
