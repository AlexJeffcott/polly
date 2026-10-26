// Structurizr's own verdict on generated DSL, for the inputs the CLI e2e
// (scripts/e2e-visualize.ts) cannot reach: deployment nodes, style tags and
// ADRs come from generator options, and no example has detected handler
// relationships. Every case here was rejected by Structurizr before its fix.
// Runs in the `verify.tools-docker` tier case; skips without docker.

import { afterAll, describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import type { ArchitectureAnalysis, ContextInfo } from "../../../analysis/src/types/architecture";
import type { MessageHandler } from "../../../analysis/src/types/core";
import { generateStructurizrDSL, type StructurizrDSLOptions } from "../codegen/structurizr";

// The consolidated successor; structurizr/cli's `validate` no-ops on bad input.
const IMAGE = "structurizr/structurizr:latest";

function dockerAvailable(): boolean {
  if (process.env["SKIP_DOCKER"] === "1") return false;
  try {
    return spawnSync("docker", ["info"], { timeout: 10_000, stdio: "ignore" }).status === 0;
  } catch {
    return false;
  }
}

const workDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-dsl-docker-"));
afterAll(() => fs.rmSync(workDir, { recursive: true, force: true }));

/** Structurizr's ERROR lines for `dsl`; it exits 0 even when it finds some. */
function validate(name: string, dsl: string): string[] {
  fs.writeFileSync(path.join(workDir, `${name}.dsl`), dsl);
  const run = spawnSync(
    "docker",
    ["run", "--rm", "-v", `${workDir}:/work`, IMAGE, "validate", "-workspace", `/work/${name}.dsl`],
    { encoding: "utf8", timeout: 120_000 }
  );
  return `${run.stdout}${run.stderr}`.split("\n").filter((l) => / ERROR /.test(l));
}

function handler(node: string, messageType: string, to?: string): MessageHandler {
  return {
    node,
    messageType,
    assignments: [],
    preconditions: [],
    postconditions: [],
    location: { file: `src/${node}/handlers.ts`, line: 1 },
    ...(to
      ? {
          relationships: [
            {
              from: `${messageType}_handler`.toLowerCase().replace(/[^a-z0-9]+/g, "_"),
              to,
              description: `${messageType} uses ${to}`,
              confidence: "high",
              evidence: [],
            },
          ],
        }
      : {}),
  };
}

function context(type: string, handlers: MessageHandler[] = []): ContextInfo {
  return {
    type,
    entryPoint: `src/${type}/index.ts`,
    handlers,
    chromeAPIs: [],
    externalAPIs: [],
    dependencies: [],
  };
}

function analysis(
  contexts: Record<string, ContextInfo> = { background: context("background") },
  extra: Partial<ArchitectureAnalysis> = {}
): ArchitectureAnalysis {
  return {
    projectRoot: "/test",
    system: { name: "Test", version: "1.0.0" },
    contexts,
    messageFlows: [],
    integrations: [],
    ...extra,
  };
}

const cases: Array<[string, ArchitectureAnalysis, StructurizrDSLOptions?]> = [
  [
    "handler-relationship",
    analysis({ background: context("background", [handler("background", "ping", "svc")]) }),
  ],
  [
    "relationships-in-two-containers",
    analysis({
      background: context("background", [handler("background", "ping", "svc")]),
      content: context("content", [handler("content", "pong", "svc")]),
    }),
    { componentDiagramContexts: ["background", "content"] },
  ],
  [
    "quote-in-message-type",
    analysis({ background: context("background", [handler("background", 'say"hi', "svc")]) }),
  ],
  [
    "types-differing-in-case",
    analysis({
      background: context("background", [
        handler("background", "Ping", "svc"),
        handler("background", "PING", "svc"),
      ]),
    }),
  ],
  [
    "types-reducing-to-one-id",
    analysis({
      background: context("background", [
        handler("background", "foo-bar", "svc"),
        handler("background", "foo_bar", "svc"),
      ]),
    }),
  ],
  [
    "deployment-environments",
    analysis(),
    { deploymentNodes: [{ name: "Browser" }, { name: "Cloud", tags: ["environment:Staging"] }] },
  ],
  [
    "deployment-environment-tag-with-space",
    analysis(),
    { deploymentNodes: [{ name: "Cloud", tags: ["environment: Pre Prod"] }] },
  ],
  [
    "deployment-quotes",
    analysis(),
    { deploymentNodes: [{ name: "Cloud", tags: ['environment:Sta"ge', 'my "tag"'] }] },
  ],
  [
    "style-tags-with-quotes",
    analysis(),
    {
      styles: {
        elements: { 'My "Tag"': { background: "#ffffff" } },
        relationships: { 'R "x"': { thickness: 2 } },
      },
    },
  ],
];

describe.skipIf(!dockerAvailable())("Structurizr accepts the generated DSL", () => {
  for (const [name, input, options] of cases) {
    test(name, () => {
      expect(validate(name, generateStructurizrDSL(input, options))).toEqual([]);
    }, 120_000);
  }

  test("ADRs", () => {
    const adrDir = path.join(workDir, "adr");
    fs.mkdirSync(adrDir, { recursive: true });
    fs.writeFileSync(
      path.join(adrDir, "0001-use-polly.md"),
      '# 1. Use "polly"\n\nDate: 2026-01-01\n\n## Status\n\nAccepted\n\n## Context\n\nWe need it.\n'
    );
    const dsl = generateStructurizrDSL(
      analysis(undefined, {
        adrs: {
          directory: "adr",
          adrs: [
            {
              id: "0001",
              title: 'Use "polly"',
              status: "accepted",
              date: "2026-01-01",
              context: "We need it.",
              decision: "Use it.",
              consequences: "",
              source: "adr/0001-use-polly.md",
            },
          ],
        },
      })
    );
    expect(validate("adrs", dsl)).toEqual([]);
  }, 120_000);
});
