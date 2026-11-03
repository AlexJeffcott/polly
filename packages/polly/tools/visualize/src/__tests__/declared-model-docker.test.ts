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
import { declaredModelDSL } from "../model/dsl";
import { STRUCTURIZR_IMAGE as IMAGE } from "../runner/export";
import { fullModel } from "./declared-model.fixture";

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

describe.skipIf(!dockerAvailable())("Structurizr accepts the DSL of a declared model", () => {
  test("the full model validates with no error", () => {
    fs.writeFileSync(
      path.join(workDir, "declared.dsl"),
      declaredModelDSL(readDeclaredModel(fullModel()))
    );
    const run = spawnSync(
      "docker",
      [
        "run",
        "--rm",
        "-v",
        `${workDir}:/work`,
        IMAGE,
        "validate",
        "-workspace",
        "/work/declared.dsl",
      ],
      { encoding: "utf8", timeout: 120_000 }
    );
    const output = `${run.stdout}${run.stderr}`;
    // Structurizr exits 0 even when it reports errors, so its ERROR lines are the verdict.
    expect(output.split("\n").filter((line) => / ERROR /.test(line))).toEqual([]);
    expect(run.status).toBe(0);
  }, 180_000);
});
