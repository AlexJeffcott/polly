// `node:path`, `fs` and `bun:sqlite` come with the runtime; no package manager
// installs them. Up to 0.97.1 every import that was not relative was reported
// as an "npm package", these included.

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { IntegrationAnalyzer } from "../integrations";

describe("IntegrationAnalyzer - runtime modules", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-integrations-runtime-"));
  });

  afterEach(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  async function technologies(source: string): Promise<Record<string, string>> {
    fs.writeFileSync(
      path.join(tempDir, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
        include: ["**/*.ts"],
      })
    );
    fs.mkdirSync(path.join(tempDir, "src"));
    fs.writeFileSync(path.join(tempDir, "src/index.ts"), source);
    const integrations = await new IntegrationAnalyzer(
      path.join(tempDir, "tsconfig.json")
    ).analyzeIntegrations();
    return Object.fromEntries(
      integrations
        .filter((i) => i.type === "external-script")
        .map((i) => [i.name, i.technology ?? ""])
    );
  }

  test("node:, bare Node built-ins, bun and bun: are runtime modules; packages stay npm", async () => {
    expect(
      await technologies(
        [
          `import * as p from "node:path";`,
          `import { readFile } from "fs/promises";`,
          `import * as fs from "node:fs";`,
          `import { Database } from "bun:sqlite";`,
          `import { file } from "bun";`,
          `import WebSocket from "ws";`,
          `import { fetch } from "undici";`,
          `import { Elysia } from "elysia";`,
          `export { p, readFile, fs, Database, file, WebSocket, fetch, Elysia };`,
        ].join("\n")
      )
    ).toEqual({
      "node:path": "Node.js built-in module",
      "node:fs": "Node.js built-in module",
      "bun:sqlite": "Bun built-in module",
      bun: "Bun built-in module",
      ws: "npm package",
      undici: "npm package",
      elysia: "npm package",
    });
  });
});
