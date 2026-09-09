import { afterAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { generateConfig } from "../codegen/config";
import { validateConfig } from "../config/parser";

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
  };

  test("generates WebSocket-specific config", () => {
    const configContent = generateConfig(mockAnalysis, "websocket-app");

    // Should include WebSocket-specific fields
    expect(configContent).toContain("maxClients");
    expect(configContent).toContain("maxMessagesPerClient");
    // Should NOT include Chrome extension fields
    expect(configContent).not.toContain("maxTabs");
    // Should include project type comment
    expect(configContent).toContain("websocket-app");
  });

  test("generates Chrome extension config (backward compatibility)", () => {
    // Test without projectConfig (legacy behavior)
    const configContent = generateConfig(mockAnalysis);

    // Should default to Chrome extension fields
    expect(configContent).toContain("maxTabs");
    expect(configContent).toContain("maxInFlight");
  });

  test("generates PWA-specific config", () => {
    const configContent = generateConfig(mockAnalysis, "pwa");

    // Should include PWA-specific fields
    expect(configContent).toContain("maxWorkers");
    expect(configContent).toContain("maxClients");
    // Should include project type comment
    expect(configContent).toContain("pwa");
  });

  test("generates Electron-specific config", () => {
    const configContent = generateConfig(mockAnalysis, "electron");

    // Should include Electron-specific fields
    expect(configContent).toContain("maxRenderers");
    // Should include project type comment
    expect(configContent).toContain("electron");
  });

  test("includes entry points in config comment", () => {
    const configContent = generateConfig(mockAnalysis, "websocket-app");

    // Should document entry points
    expect(configContent).toContain("Entry points:");
    expect(configContent).toContain("server");
  });

  test("generates valid TypeScript code", () => {
    const configContent = generateConfig(mockAnalysis, "websocket-app");

    // Should have proper imports
    expect(configContent).toContain("import { defineVerification }");
    // Should have export
    expect(configContent).toContain("export default defineVerification");
    // Should have proper structure
    expect(configContent).toContain("state: {");
    expect(configContent).toContain("messages: {");
  });
});

/**
 * polly#185: the scaffold decides a new project's `Contexts` set.
 *
 * Before this, `polly verify --setup` wrote `maxContexts: 3` for a generic
 * project — a key that emitted a constant the spec never declared — and every
 * other project type got no context key at all, so the model was over
 * `{background, content, popup}` whatever the project was.
 */
describe("the scaffold's contexts key (polly#185)", () => {
  const scaffoldTmp = fs.mkdtempSync(path.join(os.tmpdir(), "polly-185-scaffold-"));

  afterAll(() => {
    fs.rmSync(scaffoldTmp, { recursive: true, force: true });
  });

  const analysisIn = (nodes: string[]) => ({
    stateType: null,
    messageTypes: nodes.map((_n, i) => `MSG_${i}`),
    fields: [],
    handlers: nodes.map((node, i) => ({
      messageType: `MSG_${i}`,
      node,
      assignments: [],
      preconditions: [],
      postconditions: [],
      location: { file: `${node}/index.ts`, line: 1 },
    })),
  });

  test("the handler file paths decide the set when they infer one", () => {
    const content = generateConfig(analysisIn(["server", "worker"]) as never, "generic");

    expect(content).toContain("contexts: /* REVIEW */ ['server', 'worker'],");
    expect(content).toContain("Auto-configured from the file paths of the handlers");
  });

  test.each([
    ["websocket-app", "['server', 'client']"],
    ["pwa", "['ServiceWorker', 'Window']"],
    ["electron", "['main', 'renderer']"],
    ["chrome-extension", "['background', 'content', 'popup']"],
  ])("%s falls back to the contexts that project type has", (projectType, expected) => {
    const content = generateConfig(analysisIn([]) as never, projectType as never);

    expect(content).toContain(`contexts: /* REVIEW */ ${expected},`);
  });

  test("a generic project with nothing inferred leaves the key commented out", () => {
    const content = generateConfig(analysisIn([]) as never, "generic");

    expect(content).toContain("// contexts: /* CONFIGURE */ ['server'],");
    expect(content).not.toMatch(/^\s*contexts:/m);
  });

  test("no project type writes the dead maxContexts key any more", () => {
    for (const projectType of ["websocket-app", "pwa", "electron", "chrome-extension", "generic"]) {
      const content = generateConfig(analysisIn(["server"]) as never, projectType as never);
      expect(content).not.toContain("maxContexts");
    }
  });

  test("a scaffolded config validates with no context issue of its own", () => {
    // The documented entry point end to end: scaffold a config, then run the
    // validator the CLI runs on it. A scaffold that immediately warns is the
    // defect this guards.
    const content = generateConfig(analysisIn(["server", "worker"]) as never, "generic");
    const configPath = path.join(scaffoldTmp, "verification.config.ts");
    fs.writeFileSync(
      configPath,
      content
        .replace("import { defineVerification } from '@fairfox/polly/verify'", "")
        .replace("export default defineVerification({", "module.exports.verificationConfig = {")
        .replace(/\}\)\s*$/, "};")
        .replaceAll("/* REVIEW */", "")
    );

    const result = validateConfig(configPath);
    const contextIssues = result.issues.filter(
      (i) => i.field === "contexts" || i.field === "messages.maxContexts"
    );

    expect(contextIssues).toEqual([]);
  });
});
