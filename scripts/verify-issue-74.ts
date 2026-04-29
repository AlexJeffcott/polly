// End-to-end verification for issue #74.
//
// Runs TLC against two synthesised specs:
//   - "correct"     — handler writes the value its ensures() asserts
//   - "wrong-target"— handler writes a value its ensures() rejects
//
// The fix from #74 lifts ensures() into a step-temporal property so
// TLC checks postconditions on the (s, s') pair that just delivered
// the message, instead of treating them as action-body conjuncts that
// silently disable the action when they don't hold. Expected results
// after the fix:
//   - correct      → TLC reports "Model checking completed. No error."
//   - wrong-target → TLC reports a property violation
//
// Before the fix (0.33.0–0.34.0 behaviour), wrong-target also reported
// PASS — that's the regression #74 catches and this script pins.
//
// Requires Docker + the polly-tla:latest image to be available locally.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { TLAGenerator } from "../tools/verify/src/codegen/tla";
import { DockerRunner, type TLCResult } from "../tools/verify/src/runner/docker";
import type { CodebaseAnalysis, VerificationConfig } from "../tools/verify/src/types";

const MESSAGE_ROUTER_TLA = path.join(
  __dirname,
  "..",
  "tools",
  "verify",
  "specs",
  "tla",
  "MessageRouter.tla"
);

async function generateAndWriteSpec(args: {
  outDir: string;
  specName: string;
  writtenValue: string;
}): Promise<{ specPath: string; spec: string; cfg: string }> {
  const generator = new TLAGenerator();

  const config: VerificationConfig = {
    state: {
      phase: {
        type: "enum",
        values: ["disconnected", "connecting", "connected"],
      },
    },
    messages: { maxInFlight: 1, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
  };

  const analysis: CodebaseAnalysis = {
    stateType: null,
    // The handler we register below is for DISCONNECT — it must be in
    // the message-types universe or SendMessage will never produce one
    // and the property antecedent is vacuously true.
    messageTypes: ["DISCONNECT"],
    fields: [],
    handlers: [
      {
        messageType: "DISCONNECT",
        node: "background",
        // The mutation lives here. The "correct" run writes "disconnected"
        // (matching the ensures), the "wrong-target" run writes "connected"
        // (which the ensures rejects).
        assignments: [{ field: "phase", value: args.writtenValue }],
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'disconnected'",
            message: "phase must be disconnected after disconnect",
            location: { line: 1, column: 1 },
          },
        ],
        location: { file: "scripts/verify-issue-74.ts", line: 1 },
      },
    ],
    stateConstraints: [],
  };

  const { spec, cfg } = await generator.generate(config, analysis);

  const specPath = path.join(args.outDir, `${args.specName}.tla`);
  const cfgPath = path.join(args.outDir, `${args.specName}.cfg`);
  fs.writeFileSync(specPath, spec);
  fs.writeFileSync(cfgPath, cfg);

  // TLC needs MessageRouter.tla alongside the user spec.
  fs.copyFileSync(MESSAGE_ROUTER_TLA, path.join(args.outDir, "MessageRouter.tla"));

  return { specPath, spec, cfg };
}

async function ensurePrerequisites(docker: DockerRunner): Promise<void> {
  if (!(await docker.isDockerAvailable())) {
    console.log("Docker is not running. Start Docker Desktop and try again.");
    process.exit(2);
  }
  if (!(await docker.hasImage())) {
    console.log("polly-tla:latest image is missing. Run `polly verify` once to build it.");
    process.exit(2);
  }
  if (!fs.existsSync(MESSAGE_ROUTER_TLA)) {
    console.log(`MessageRouter.tla not found at ${MESSAGE_ROUTER_TLA}`);
    process.exit(2);
  }
}

function reportWrongResult(wrongResult: TLCResult, wrongFails: boolean): void {
  if (wrongFails) {
    const violationLine =
      wrongResult.output
        .split("\n")
        .find((l) => l.includes("violated") || l.includes("EnsuresAfter")) ?? "";
    if (violationLine) {
      console.log(`  ${violationLine.trim()}`);
    }
    return;
  }
  console.log("  ── output ──");
  console.log(wrongResult.output);
}

async function main(): Promise<void> {
  const docker = new DockerRunner();
  await ensurePrerequisites(docker);

  const correctDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-i74-correct-"));
  const wrongDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-i74-wrong-"));

  console.log("→ Generating specs");
  const correct = await generateAndWriteSpec({
    outDir: correctDir,
    specName: "UserApp",
    writtenValue: "disconnected",
  });
  const wrong = await generateAndWriteSpec({
    outDir: wrongDir,
    specName: "UserApp",
    writtenValue: "connected",
  });

  console.log(`  correct  → ${correct.specPath}`);
  console.log(`  wrong    → ${wrong.specPath}`);

  console.log("→ Running TLC on the correct spec");
  const correctResult = await docker.runTLC(correct.specPath, { timeout: 60_000 });
  const correctPass = correctResult.success === true;
  console.log(`  correct: ${correctPass ? "PASS ✓" : "FAIL ✗"}`);
  if (!correctPass) {
    console.log("  ── output ──");
    console.log(correctResult.output);
  }

  console.log("→ Running TLC on the wrong-target spec");
  const wrongResult = await docker.runTLC(wrong.specPath, { timeout: 60_000 });
  // parseTLCOutput only matches "Error: Invariant ..." today; for property
  // violations we look for them in the raw output.
  const propertyViolated =
    wrongResult.output.includes("Temporal properties were violated") ||
    wrongResult.output.includes("EnsuresAfter_") ||
    wrongResult.output.includes("Error: Invariant EnsuresAfter_");
  const wrongFails = wrongResult.success === false && propertyViolated;
  console.log(`  wrong-target: ${wrongFails ? "FAIL (as expected) ✓" : "UNEXPECTED PASS ✗"}`);
  reportWrongResult(wrongResult, wrongFails);

  // Clean up unless something failed (keep artefacts around for inspection)
  const allOk = correctPass && wrongFails;
  if (allOk) {
    fs.rmSync(correctDir, { recursive: true, force: true });
    fs.rmSync(wrongDir, { recursive: true, force: true });
  } else {
    console.log(`  artefacts kept: ${correctDir}, ${wrongDir}`);
  }

  if (!allOk) {
    console.log("\nIssue #74 verification FAILED.");
    process.exit(1);
  }
  console.log("\nIssue #74 verification PASSED — wrong-target writes are caught by TLC.");
}

main().catch((err) => {
  console.log(err);
  process.exit(1);
});
