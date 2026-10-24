// A test that calls the app over HTTP is not an external integration of the
// app. `fetch("http://localhost:3000")` in elysia-todo-app's api.test.ts was
// drawn as a `localhost_api` the server "Calls", and the visualize e2e had a
// relationship minimum that counted it.

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { IntegrationAnalyzer } from "../integrations";

describe("IntegrationAnalyzer - test files", () => {
  let rootDir: string;
  let tempDir: string;

  beforeEach(() => {
    rootDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-integrations-test-"));
    tempDir = rootDir;
  });

  afterEach(() => {
    fs.rmSync(rootDir, { recursive: true, force: true });
  });

  function run(files: Record<string, string>) {
    fs.writeFileSync(
      path.join(tempDir, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
        include: ["**/*.ts"],
      })
    );
    for (const [rel, content] of Object.entries(files)) {
      const full = path.join(tempDir, rel);
      fs.mkdirSync(path.dirname(full), { recursive: true });
      fs.writeFileSync(full, content);
    }
    return new IntegrationAnalyzer(path.join(tempDir, "tsconfig.json")).analyzeIntegrations();
  }

  test("a fetch in application source is an integration", async () => {
    const integrations = await run({
      "src/weather.ts": `export const load = () => fetch("https://api.weather.example/today");`,
    });
    expect(integrations.map((i) => i.url)).toEqual(["https://api.weather.example"]);
  });

  test("a project that itself lives under a __tests__ directory still counts", async () => {
    tempDir = path.join(rootDir, "__tests__", "fixtures", "app");
    fs.mkdirSync(tempDir, { recursive: true });
    const integrations = await run({
      "src/weather.ts": `export const load = () => fetch("https://api.weather.example/today");`,
    });
    expect(integrations.map((i) => i.url)).toEqual(["https://api.weather.example"]);
  });

  test.each([
    "src/__tests__/api.ts",
    "src/api.test.ts",
    "src/api.spec.ts",
    "tests/api.ts",
    "e2e/api.ts",
  ])("fetch and WebSocket in %s are not integrations", async (rel) => {
    const integrations = await run({
      [rel]: `
        export const a = () => fetch("http://localhost:3000/todos");
        export const b = () => new WebSocket("ws://localhost:3000/polly/ws");
      `,
    });
    expect(integrations).toEqual([]);
  });
});
