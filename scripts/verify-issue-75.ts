// End-to-end verification for issue #75.
//
// Issue #75 reported that the `EnsuresAfter_*` step-temporal property
// emitted from 0.35.0 false-positives whenever a message has more than
// one target. The property quantified `\A target \in messages[m].targets`
// over the whole target set, but routing only mutates one target at a
// time (chosen by `\E target`), so siblings retain their pre-step state
// and any predicate that is not the init-default value of the field
// fails on those untouched targets.
//
// The fix records the routed target in a new `messages[m].deliveredTo`
// field and binds the property's `target` via LET to that value, so the
// predicate fires only against the target the action actually wrote.
//
// Two specs are checked:
//   - "multi-target-correct" — handler writes the value its ensures()
//     asserts; message is sent to a SUBSET that may include all three
//     contexts. Pre-fix this fails spuriously; post-fix it passes.
//   - "multi-target-wrong"   — handler writes the wrong value; the
//     property must still trip. This pins #74's catch.
//
// Requires Docker + the polly-tla:latest image.

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

  // Default Contexts is {background, content, popup} — three contexts,
  // which is exactly what reproduces #75: SendMessage explores every
  // non-empty SUBSET of Contexts as the target set, so multi-target
  // sends are sampled by TLC.
  const config: VerificationConfig = {
    state: {
      phase: {
        type: "enum",
        values: ["disconnected", "connecting", "connected"],
      },
    },
    messages: { maxInFlight: 2, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
  };

  const analysis: CodebaseAnalysis = {
    stateType: null,
    messageTypes: ["CONNECT"],
    fields: [],
    handlers: [
      {
        messageType: "CONNECT",
        node: "background",
        // The init value of phase is "disconnected"; the ensures asserts
        // a non-init value. Without the #75 fix, the property check
        // against untouched sibling targets would still see init
        // "disconnected" and fail the `phase = "connected"` predicate.
        assignments: [{ field: "phase", value: args.writtenValue }],
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'connected'",
            message: "phase must be connected after CONNECT",
            location: { line: 1, column: 1 },
          },
        ],
        location: { file: "scripts/verify-issue-75.ts", line: 1 },
      },
    ],
    stateConstraints: [],
  };

  const { spec, cfg } = await generator.generate(config, analysis);

  const specPath = path.join(args.outDir, `${args.specName}.tla`);
  const cfgPath = path.join(args.outDir, `${args.specName}.cfg`);
  fs.writeFileSync(specPath, spec);
  fs.writeFileSync(cfgPath, cfg);

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

function reportResult(label: string, result: TLCResult, expectedFail: boolean): boolean {
  const propertyViolated =
    result.output.includes("Temporal properties were violated") ||
    result.output.includes("EnsuresAfter_") ||
    result.output.includes("Error: Invariant EnsuresAfter_");
  const failed = result.success === false && propertyViolated;

  if (expectedFail) {
    console.log(`  ${label}: ${failed ? "FAIL (as expected) ✓" : "UNEXPECTED PASS ✗"}`);
    if (failed) {
      const violationLine =
        result.output
          .split("\n")
          .find((l) => l.includes("violated") || l.includes("EnsuresAfter")) ?? "";
      if (violationLine) console.log(`    ${violationLine.trim()}`);
    } else {
      console.log("    ── output ──");
      console.log(result.output);
    }
    return failed;
  }

  const passed = result.success === true;
  console.log(`  ${label}: ${passed ? "PASS ✓" : "FAIL ✗"}`);
  if (!passed) {
    console.log("    ── output ──");
    console.log(result.output);
  }
  return passed;
}

async function main(): Promise<void> {
  const docker = new DockerRunner();
  await ensurePrerequisites(docker);

  const correctDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-i75-correct-"));
  const wrongDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-i75-wrong-"));

  console.log(
    "→ Generating specs (multi-context, default Contexts = {background, content, popup})"
  );
  const correct = await generateAndWriteSpec({
    outDir: correctDir,
    specName: "UserApp",
    writtenValue: "connected",
  });
  const wrong = await generateAndWriteSpec({
    outDir: wrongDir,
    specName: "UserApp",
    writtenValue: "connecting",
  });

  console.log(`  correct → ${correct.specPath}`);
  console.log(`  wrong   → ${wrong.specPath}`);

  console.log("→ Running TLC on the multi-target correct spec");
  const correctResult = await docker.runTLC(correct.specPath, { timeout: 300_000 });
  const correctOk = reportResult("multi-target-correct", correctResult, false);

  console.log("→ Running TLC on the multi-target wrong spec");
  const wrongResult = await docker.runTLC(wrong.specPath, { timeout: 300_000 });
  const wrongOk = reportResult("multi-target-wrong", wrongResult, true);

  const allOk = correctOk && wrongOk;
  if (allOk) {
    fs.rmSync(correctDir, { recursive: true, force: true });
    fs.rmSync(wrongDir, { recursive: true, force: true });
  } else {
    console.log(`  artefacts kept: ${correctDir}, ${wrongDir}`);
  }

  if (!allOk) {
    console.log("\nIssue #75 verification FAILED.");
    process.exit(1);
  }
  console.log("\nIssue #75 verification PASSED — multi-target sends no longer false-positive.");
}

main().catch((err) => {
  console.log(err);
  process.exit(1);
});
