#!/usr/bin/env bun
// polly#160 end-to-end: prove that the generated capability invariant actually
// makes TLC report a counterexample.
//
// Runs real TLC-in-Docker (needs the `polly-tla:latest` image; build with the
// CLI's normal Docker setup if missing) against the capability-guard fixture:
//
//   1. WITH the capability declared → TLC must REPORT a violation of
//      Capability_canSend (the REGISTER path grants canSend without
//      authenticated — the #160 bug).
//   2. WITHOUT the capability (falsification) → TLC must PASS, proving the
//      failure in (1) is caused by the capability invariant, not the model.
//
// This is the committed verification artefact (CLAUDE.md): one command, prints
// a specific success/failure. It is a script, not a unit test, because it needs
// Docker.

import { copyFileSync, existsSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { analyzeCodebase } from "../../analysis/src";
import { generateTLA } from "../src/codegen/tla";
import { DockerRunner } from "../src/runner/docker";
import type { VerificationConfig } from "../src/types";

const root = path.join(import.meta.dir, "..");
const fixture = path.join(root, "test-projects", "capability-guard");
const baseSpec = path.join(root, "specs", "tla", "MessageRouter.tla");

const baseConfig: VerificationConfig = {
  state: {
    "session.authenticated": { type: "boolean" },
    "session.canSend": { type: "boolean" },
  },
  coupledFields: [["session.authenticated", "session.canSend"]],
  messages: { maxInFlight: 1, maxTabs: 1 },
  onBuild: "warn",
  onRelease: "error",
};

const capability = {
  name: "canSend",
  enabledBy: "session.value.canSend",
  requires: "session.value.authenticated",
  message: "sends require an authenticated session",
};

async function runCase(label: string, config: VerificationConfig) {
  const analysis = await analyzeCodebase({
    tsConfigPath: path.join(fixture, "tsconfig.json"),
  });
  const { spec, cfg } = await generateTLA(config, analysis);

  const work = mkdtempSync(path.join(tmpdir(), "polly-capguard-"));
  writeFileSync(path.join(work, "UserApp.tla"), spec);
  writeFileSync(path.join(work, "UserApp.cfg"), cfg);
  copyFileSync(baseSpec, path.join(work, "MessageRouter.tla"));

  const docker = new DockerRunner();
  const result = await docker.runTLC(path.join(work, "UserApp.tla"), {
    workers: 1,
    timeout: 120_000,
  });

  console.log(`\n[${label}]`);
  console.log(`  success: ${result.success}`);
  console.log(`  violation: ${result.violation?.name ?? "none"}`);
  if (result.error) console.log(`  error: ${result.error}`);
  return result;
}

async function main() {
  if (!existsSync(baseSpec)) throw new Error(`base spec not found: ${baseSpec}`);

  const docker = new DockerRunner();
  if (!(await docker.isDockerAvailable()) || !(await docker.hasImage())) {
    // biome-ignore lint/suspicious/noConsole: e2e script needs console output
    console.error(
      "❌ Docker or the polly-tla:latest image is unavailable. Build it via `polly verify` setup first."
    );
    process.exit(2);
  }

  // 1. With the capability: TLC must find the counterexample.
  const withCap = await runCase("with capability (expect VIOLATION)", {
    ...baseConfig,
    capabilities: [capability],
  });

  // 2. Falsification — without the capability: TLC must pass.
  const withoutCap = await runCase("without capability (expect PASS)", baseConfig);

  const flaggedRight = withCap.violation?.name?.includes("Capability_canSend") === true;
  const passesWithout = withoutCap.success === true;

  console.log("\n──────────────────────────────────────────");
  if (flaggedRight && passesWithout) {
    console.log("✅ e2e PASS: the capability invariant catches the REGISTER bug,");
    console.log("   and removing it makes the same model pass (falsification).");
    process.exit(0);
  }
  console.log("❌ e2e FAIL:");
  if (!flaggedRight) {
    console.log(
      `   expected a Capability_canSend violation WITH the capability; got ${withCap.violation?.name ?? "none"}.`
    );
  }
  if (!passesWithout) {
    console.log("   expected PASS WITHOUT the capability; the model failed for another reason.");
  }
  process.exit(1);
}

await main();
