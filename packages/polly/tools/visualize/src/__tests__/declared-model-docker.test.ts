// Structurizr's own verdict on the DSL a declared model writes. The fixture
// uses every part of the model, so a writer change that breaks any construct
// fails here. Runs in the `verify.tools-docker` tier case; skips without
// docker, like dsl-structurizr-docker.test.ts.

import { afterAll, describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { readDeclaredModel } from "../model/check";
import { declaredModelDSL, declaredModelFragment } from "../model/dsl";
import { STRUCTURIZR_IMAGE as IMAGE } from "../runner/export";
import { fullModel, HOST_WORKSPACE, hostedModel } from "./declared-model.fixture";

function dockerAvailable(): boolean {
  if (process.env["SKIP_DOCKER"] === "1") return false;
  try {
    return spawnSync("docker", ["info"], { timeout: 10_000, stdio: "ignore" }).status === 0;
  } catch {
    return false;
  }
}

const workDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-declared-docker-"));
afterAll(() => fs.rmSync(workDir, { recursive: true, force: true }));

/** Structurizr's ERROR lines for the workspace at `file` under workDir; it exits 0 even with errors. */
function structurizrErrors(file: string): { errors: string[]; status: number | null } {
  const run = spawnSync(
    "docker",
    ["run", "--rm", "-v", `${workDir}:/work`, IMAGE, "validate", "-workspace", `/work/${file}`],
    { encoding: "utf8", timeout: 120_000 }
  );
  const output = `${run.stdout}${run.stderr}`;
  return { errors: output.split("\n").filter((line) => / ERROR /.test(line)), status: run.status };
}

describe.skipIf(!dockerAvailable())("Structurizr accepts the DSL of a declared model", () => {
  test("the full model validates with no error", () => {
    fs.writeFileSync(
      path.join(workDir, "declared.dsl"),
      declaredModelDSL(readDeclaredModel(fullModel()))
    );
    expect(structurizrErrors("declared.dsl")).toEqual({ errors: [], status: 0 });
  }, 180_000);

  test("a workspace that owns the hosted model's refs validates with its fragment included", () => {
    const fragment = declaredModelFragment(readDeclaredModel(hostedModel()));
    fs.mkdirSync(path.join(workDir, "fragment"), { recursive: true });
    fs.writeFileSync(path.join(workDir, "fragment", "model.dsl"), fragment.model);
    fs.writeFileSync(path.join(workDir, "fragment", "views.dsl"), fragment.views);
    fs.writeFileSync(path.join(workDir, "host.dsl"), HOST_WORKSPACE);
    expect(structurizrErrors("host.dsl")).toEqual({ errors: [], status: 0 });
  }, 180_000);
});
