// `polly visualize generate --model`: the checker refuses every malformed or
// dangling part of a declared model, the writer writes exactly what the model
// declares, and the CLI entry point a user runs ties the two to the file it
// writes. Structurizr's own verdict on the written DSL is in
// declared-model-docker.test.ts.

import { afterAll, describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { DeclaredModelError, readDeclaredModel } from "../model/check";
import { declaredModelDSL } from "../model/dsl";
import type { DeclaredModel } from "../model/types";
import { fullModel } from "./declared-model.fixture";

/** The problems readDeclaredModel reports for `value`; none where it accepts it. */
function problemsOf(value: unknown): string[] {
  try {
    readDeclaredModel(value);
    return [];
  } catch (error) {
    if (error instanceof DeclaredModelError) return error.problems;
    throw error;
  }
}

function changed(change: (model: DeclaredModel) => void): DeclaredModel {
  const model = fullModel();
  change(model);
  return model;
}

describe("readDeclaredModel", () => {
  test("accepts the full model unchanged", () => {
    expect(readDeclaredModel(fullModel())).toEqual(fullModel());
  });

  test("refuses a value that is not an object", () => {
    expect(problemsOf(null)).toEqual(["the model must be an object"]);
  });

  test("refuses a model with no system and no view", () => {
    const problems = problemsOf({
      name: "Empty",
      people: [],
      systems: [],
      relationships: [],
      views: [],
    });
    expect(problems).toContain("systems must hold at least one software system");
    expect(problems).toContain("views must hold at least one view");
  });

  test("reports every shape problem in one run", () => {
    const problems = problemsOf({
      name: "",
      people: [{ id: "1st", name: "Reader", colour: "red" }],
      systems: [{ id: "parts", name: "Parts" }],
      relationships: "none",
      views: [{ kind: "systemContext", system: "parts", key: "bad key", layout: "diagonal" }],
    });
    expect(problems).toEqual([
      "people[0].colour is not a known field; known: id, name, description, tags",
      'people[0].id "1st" must start with a letter and hold only letters, digits and _',
      "relationships must be an array",
      'views[0].key "bad key" must hold only letters, digits, _ and -',
      "views[0].layout must be one of lr, rl, tb, bt",
      "views must hold at least one view",
      "name must be a non-empty string",
    ]);
  });

  test("refuses a line break in any text", () => {
    const model = changed((m) => {
      m.people[0] = { id: "reader", name: "Two\nlines" };
    });
    expect(problemsOf(model)).toEqual(["people[0].name must not contain a line break"]);
  });

  test("refuses a tag holding a comma, since the DSL joins tags with commas", () => {
    const model = changed((m) => {
      m.people[1] = { id: "engineer", name: "Engineer", tags: ["a,b"] };
    });
    expect(problemsOf(model)).toEqual(['people[1].tags[0] "a,b" must not contain a comma']);
  });

  test("refuses an id declared twice", () => {
    const model = changed((m) => {
      m.people.push({ id: "shell", name: "Second shell" });
    });
    expect(problemsOf(model)).toEqual(['id "shell" is declared more than once']);
  });

  test("refuses a relationship to an undeclared element, to itself, or repeated", () => {
    const model = changed((m) => {
      m.relationships.push(
        { from: "unit", to: "ghost", description: "Calls" },
        { from: "unit", to: "unit", description: "Calls itself" },
        { from: "reader", to: "page", description: "Reads pages in" }
      );
    });
    expect(problemsOf(model)).toEqual([
      'relationships[12].to "ghost" names no element',
      'relationships[13] runs from "unit" to itself',
      'relationships[14] repeats reader -> page "Reads pages in"',
    ]);
  });

  test("refuses a view whose subject is the wrong kind of element", () => {
    const model = changed((m) => {
      m.views = [
        { kind: "systemContext", system: "shell", key: "A", layout: "lr" },
        { kind: "component", container: "parts", key: "B", layout: "lr" },
        { kind: "deployment", scope: "unit", environment: "prod", key: "C", layout: "lr" },
      ];
    });
    expect(problemsOf(model)).toEqual([
      'views[0].system "shell" is not a software system',
      'views[1].container "parts" is not a container',
      'views[2].scope "unit" is not a software system or "*"',
      'views[2].environment "prod" names no deployment environment',
    ]);
  });

  test("refuses a dynamic step with no matching relationship, or naming its own scope", () => {
    const model = changed((m) => {
      m.views = [
        {
          kind: "dynamic",
          scope: "shell",
          key: "Steps",
          layout: "lr",
          steps: [
            { from: "unit", to: "page", description: "Answers" },
            { from: "loader", to: "shell", description: "Starts" },
          ],
        },
      ];
    });
    expect(problemsOf(model)).toEqual([
      "views[0].steps[0] unit -> page matches no declared relationship",
      "views[0].steps[1] loader -> shell matches no declared relationship",
      'views[0].steps[1] names the view\'s own scope "shell"',
    ]);
  });

  test("refuses two views with one key", () => {
    const model = changed((m) => {
      m.views.push({ kind: "container", system: "host", key: "Containers", layout: "lr" });
    });
    expect(problemsOf(model)).toEqual(['views[5].key "Containers" is used by another view']);
  });

  test("refuses a deployment that runs a non-container, or reuses a node name under one parent", () => {
    const model = changed((m) => {
      m.deployments = [
        {
          id: "qa",
          name: "QA",
          nodes: [
            { name: "Browser", containers: ["bus"] },
            { name: "Browser", containers: ["page"] },
          ],
        },
      ];
    });
    expect(problemsOf(model)).toEqual([
      'deployments[0].nodes[0].containers names "bus", which is not a container',
      'deployments[0].nodes[1].name "Browser" is used twice under one parent',
    ]);
  });

  test("refuses unknown style properties and values", () => {
    const model: unknown = {
      ...fullModel(),
      styles: {
        elements: { Unit: { shape: "Star", background: "green", stroke: 1 } },
        relationships: { Dom: { routing: "Wiggly" } },
      },
    };
    expect(problemsOf(model)).toEqual([
      'styles.elements["Unit"].stroke is not a known field; known: shape, icon, width, height, background, color, fontSize, border, opacity, metadata, description',
      'styles.elements["Unit"].shape must be one of Box, RoundedBox, Circle, Ellipse, Hexagon, Cylinder, Component, Person, Robot, Folder, WebBrowser, MobileDevicePortrait, MobileDeviceLandscape, Pipe',
      'styles.elements["Unit"].background must be a colour as #rrggbb',
      'styles.relationships["Dom"].routing must be one of Direct, Orthogonal, Curved',
    ]);
  });
});

describe("declaredModelDSL", () => {
  const dsl = declaredModelDSL(fullModel());

  test("writes each element with its positional arguments, keeping positions for absent ones", () => {
    expect(dsl).toContain('    reader = person "Reader" "Reads pages."');
    expect(dsl).toContain('    engineer = person "Engineer" "" "Staff"');
    expect(dsl).toContain('      renderer = container "Page renderer" "" "Node"');
    expect(dsl).toContain('      unit = container "Unit" "" "" "Browser,Unit"');
    expect(dsl).toContain('        bus = component "Bus" "" "shell/src/store.ts"');
    expect(dsl).toContain('    ci = softwareSystem "CI" "" "External"');
  });

  test("escapes quotes in text", () => {
    expect(dsl).toContain('element = component "Unit element" "Places a \\"unit\\"."');
  });

  test("writes every relationship and no other", () => {
    const arrows = dsl.split("\n").filter((line) => /^ {4}\w+ -> \w+ /.test(line));
    expect(arrows).toHaveLength(fullModel().relationships.length);
    expect(dsl).toContain('    page -> element "Places a unit element" "" "Dom"');
  });

  test("writes nested deployment nodes with their container instances", () => {
    expect(dsl).toContain('    qa = deploymentEnvironment "QA" {');
    expect(dsl).toContain('      deploymentNode "Browser" "" "Chrome" {');
    expect(dsl).toContain("        containerInstance shell");
    expect(dsl).toContain('          deploymentNode "S3" {');
  });

  test("writes each view with its stated layout and dynamic steps in order", () => {
    expect(dsl).toContain('    component shell "ShellComponents" {');
    expect(dsl).toContain("      autoLayout tb");
    expect(dsl).toContain('    deployment * qa "QADeployment" {');
    const steps = dsl.split("\n").filter((line) => /^ {6}\w+ -> \w+ /.test(line));
    expect(steps).toEqual(
      fullModel()
        .views.flatMap((v) => (v.kind === "dynamic" ? v.steps : []))
        .map((s) => `      ${s.from} -> ${s.to} "${s.description}"`)
    );
  });

  test("tells the viewer to keep the views in the order the model declares", () => {
    expect(dsl).toContain('    properties {\n      "structurizr.sort" "created"\n    }');
  });

  test("writes only the styles the model declares", () => {
    expect(dsl).toContain('      element "External" {');
    expect(dsl).toContain("        border Dashed");
    expect(dsl).toContain("        metadata false");
    expect(dsl).toContain('      relationship "Dom" {');
    expect(dsl).not.toContain('element "Container"');
  });

  test("writes no styles block for a model with no styles", () => {
    const { styles: _styles, ...unstyled } = fullModel();
    expect(declaredModelDSL(unstyled)).not.toContain("styles {");
  });
});

describe("polly visualize generate --model, through the CLI", () => {
  const CLI = path.resolve(import.meta.dir, "..", "cli.ts");
  const FIXTURE = path.resolve(import.meta.dir, "declared-model.fixture.ts");
  const workDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-declared-model-"));
  afterAll(() => fs.rmSync(workDir, { recursive: true, force: true }));

  /** A fresh project directory holding `model.ts` with the given body. */
  function project(name: string, body: string): string {
    const dir = path.join(workDir, name);
    fs.mkdirSync(dir);
    fs.writeFileSync(path.join(dir, "model.ts"), body);
    return dir;
  }

  function generate(cwd: string, ...args: string[]): { status: number | null; stderr: string } {
    const run = spawnSync("bun", [CLI, "generate", ...args], {
      cwd,
      encoding: "utf8",
      env: { ...process.env, NO_COLOR: "1" },
      timeout: 60_000,
    });
    return { status: run.status, stderr: run.stderr };
  }

  const dslIn = (dir: string): string => path.join(dir, "docs", "architecture.dsl");

  test("writes docs/architecture.dsl from the model the file declares", () => {
    const dir = project(
      "valid",
      `import { fullModel } from ${JSON.stringify(FIXTURE)};\nexport default async () => fullModel();\n`
    );
    const run = generate(dir, "--model", "model.ts");
    expect(run.stderr).toBe("");
    expect(run.status).toBe(0);
    expect(fs.readFileSync(dslIn(dir), "utf8")).toBe(
      declaredModelDSL(readDeclaredModel(fullModel()))
    );
  });

  test("refuses a model with problems, lists them, and writes no DSL", () => {
    const dir = project(
      "invalid",
      `import { fullModel } from ${JSON.stringify(FIXTURE)};\nexport default () => ({ ...fullModel(), relationships: [{ from: "unit", to: "ghost", description: "Calls" }], views: fullModel().views.slice(0, 3) });\n`
    );
    const run = generate(dir, "--model=model.ts");
    expect(run.status).toBe(1);
    expect(run.stderr).toContain("Declared model refused");
    expect(run.stderr).toContain('relationships[0].to "ghost" names no element');
    expect(fs.existsSync(dslIn(dir))).toBe(false);
  });

  test("refuses a file whose default export is not a function", () => {
    const dir = project("object", "export default { name: 'Parts' };\n");
    const run = generate(dir, "--model", "model.ts");
    expect(run.status).toBe(1);
    expect(run.stderr).toContain("must default-export a function that returns the model");
    expect(fs.existsSync(dslIn(dir))).toBe(false);
  });

  test("refuses a model file that does not exist", () => {
    const dir = project("missing", "");
    const run = generate(dir, "--model", "absent.ts");
    expect(run.status).toBe(1);
    expect(run.stderr).toContain("absent.ts, which does not exist");
  });

  test("refuses --model together with --snapshot", () => {
    const dir = project("both", "");
    const run = generate(dir, "--model", "model.ts", "--snapshot", "snapshot.json");
    expect(run.status).toBe(1);
    expect(run.stderr).toContain("--model and --snapshot cannot be combined");
  });

  test("refuses --model with no path, and an unknown option", () => {
    const dir = project("flags", "");
    expect(generate(dir, "--model").stderr).toContain("--model requires a file path");
    expect(generate(dir, "--model=").stderr).toContain("--model requires a file path");
    expect(generate(dir, "--colour").stderr).toContain("Unknown option for generate: --colour");
  });
});
