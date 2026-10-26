// Extractor inputs to `polly visualize --generate` that produced wrong or
// Structurizr-invalid DSL for the examples:
//   - a file comment opening `/**` on its own line became the container
//     description "/**" (blob-share, team-task-manager, full-featured);
//   - message sends in BDD steps and tests became flows from `unknown` or
//     from the server to itself (todo-list, team-task-manager);
//   - several handlers for one type in one context listed that context twice
//     as a recipient (webrtc-p2p-chat);
//   - a popup page under src/ was never found, so flows from it pointed at a
//     container that was never declared (full-featured, todo-list);
//   - a type guard narrowing an object literal became a handler named after
//     the literal (full-featured popup);
//   - a sibling workspace package was listed as an external npm dependency
//     (elysia-todo-app).

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import type { MessageHandler } from "../../types/core";
import { commentTextLines } from "../contexts";
import { FlowAnalyzer } from "../flows";
import { HandlerExtractor } from "../handlers";
import { IntegrationAnalyzer } from "../integrations";
import { ManifestParser } from "../manifest";

let dir: string;

beforeEach(() => {
  dir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-viz-sources-"));
});

afterEach(() => {
  fs.rmSync(dir, { recursive: true, force: true });
});

function write(files: Record<string, string>): string {
  for (const [rel, content] of Object.entries(files)) {
    const full = path.join(dir, rel);
    fs.mkdirSync(path.dirname(full), { recursive: true });
    fs.writeFileSync(full, content);
  }
  const tsconfig = path.join(dir, "tsconfig.json");
  fs.writeFileSync(
    tsconfig,
    JSON.stringify({
      compilerOptions: {
        target: "ES2022",
        module: "ESNext",
        moduleResolution: "bundler",
        strict: true,
      },
      include: ["**/*.ts"],
    })
  );
  return tsconfig;
}

function handler(node: string, messageType: string): MessageHandler {
  return {
    node,
    messageType,
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: path.join(dir, "src", node, "handlers.ts"), line: 1 },
  };
}

describe("commentTextLines", () => {
  test("a JSDoc opener on its own line is not text", () => {
    const lines = commentTextLines("/**\n * Blob-share example server.\n *\n * More.\n */");
    expect(lines.filter(Boolean)).toEqual(["Blob-share example server.", "More."]);
  });

  test("text on the opener line is kept", () => {
    expect(commentTextLines("/** Bun bundles a CSS import. */").filter(Boolean)).toEqual([
      "Bun bundles a CSS import.",
    ]);
  });

  test("a line comment loses its slashes", () => {
    expect(commentTextLines("// Background script entry point")).toEqual([
      "Background script entry point",
    ]);
  });
});

describe("FlowAnalyzer", () => {
  test("a send from a test or BDD step file is not a flow", async () => {
    const tsconfig = write({
      "src/popup/index.ts": `declare const bus: { send(m: unknown): void };\nbus.send({ type: "LOGIN" });\n`,
      "features/steps.ts": `declare const bus: { send(m: unknown): void };\nbus.send({ type: "LOGIN" });\n`,
      "src/popup/index.test.ts": `declare const bus: { send(m: unknown): void };\nbus.send({ type: "LOGIN" });\n`,
    });
    const flows = await new FlowAnalyzer(tsconfig, [handler("background", "LOGIN")]).analyzeFlows();
    expect(flows.map((f) => f.from)).toEqual(["popup"]);
  });

  test("several handlers in one context make that context one recipient", async () => {
    const tsconfig = write({
      "src/client/peer.ts": `declare const ws: { send(m: unknown): void };\nws.send({ type: "offer" });\n`,
    });
    const flows = await new FlowAnalyzer(tsconfig, [
      handler("server", "offer"),
      handler("server", "offer"),
      handler("client", "offer"),
    ]).analyzeFlows();
    expect(flows).toHaveLength(1);
    expect(flows[0]?.to).toEqual(["server", "client"]);
  });
});

describe("ManifestParser popup under src/", () => {
  test("the manifest's built page path is found in src/", () => {
    fs.writeFileSync(
      path.join(dir, "manifest.json"),
      JSON.stringify({
        manifest_version: 3,
        name: "x",
        version: "1",
        action: { default_popup: "popup/popup.html" },
        options_page: "options/options.html",
      })
    );
    write({
      "src/popup/popup.html": `<html><body><script type="module" src="./index.js"></script></body></html>`,
      "src/popup/index.tsx": "export {};\n",
      "src/options/options.html": "<html></html>",
      "src/options/index.tsx": "export {};\n",
    });
    const entryPoints = new ManifestParser(dir).getContextEntryPoints();
    expect(entryPoints["popup"]).toBe(path.join(dir, "src", "popup", "index.tsx"));
    expect(entryPoints["options"]).toBe(path.join(dir, "src", "options", "index.tsx"));
  });
});

describe("HandlerExtractor type guards", () => {
  test("a guard narrowing an object literal type is not a handler", async () => {
    const tsconfig = write({
      "src/popup/index.ts": `
interface LoginMessage { type: "login" }
function isLoginMessage(m: unknown): m is LoginMessage {
  return typeof m === "object" && m !== null && (m as { type?: string }).type === "login";
}
function isSuccess(v: unknown): v is { success: true } {
  return v !== null && typeof v === "object" && "success" in v;
}
export function onResult(v: unknown) {
  if (isSuccess(v)) {
    console.log("ok");
  }
  if (isLoginMessage(v)) {
    console.log("login");
  }
}
`,
    });
    const { handlers } = await new HandlerExtractor(tsconfig).extractHandlers();
    const types = handlers.map((h) => h.messageType);
    expect(types).toContain("login");
    expect(types.some((t) => t.includes("{"))).toBe(false);
  });
});

describe("IntegrationAnalyzer internal packages", () => {
  test("an import of one of the project's own packages is not an integration", async () => {
    const tsconfig = write({
      "client/src/api.ts": `import type { App } from "my-app-server";\nimport { treaty } from "@elysiajs/eden";\nexport type { App };\nexport { treaty };\n`,
    });
    const names = async (internal: string[]) =>
      (await new IntegrationAnalyzer(tsconfig, internal).analyzeIntegrations()).map((i) => i.name);
    expect(await names([])).toEqual(["my-app-server", "@elysiajs/eden"]);
    expect(await names(["my-app-server", "my-app-client"])).toEqual(["@elysiajs/eden"]);
  });
});
