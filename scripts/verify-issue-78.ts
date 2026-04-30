// End-to-end verification for issue #78.
//
// Issue #74 lifted ensures() into a step-temporal property so TLC catches
// wrong-target writes on a (s, s') pair. That fix only fires for handlers
// TLC actually reaches. A handler that requires another handler to have
// fired first — handleDisconnected only enabled after StartConnecting and
// FinishConnecting, becomeLeader only after a chain of three messages —
// has its EnsuresAfter_* property registered in the spec but never
// evaluated, because the global maxInFlight: 1 keeps the message queue
// too shallow to produce the multi-step pre-state.
//
// Issue #78 adds per-subsystem bounds so a payload-free subsystem can
// run at higher maxInFlight without forcing every other subsystem to
// pay the same exploration cost. This script pins that the bounds
// override actually changes which postconditions TLC checks.
//
// Test bed — minimal connection state machine:
//   Connect      phase: any → connected
//   Disconnect   requires phase = connected; sets phase = disconnected
//                ensures phase' = disconnected
//
// Disconnect is two-step-reachable: Connect must fire first to satisfy
// its precondition. Under bounds.maxInFlight: 1 TLC never produces a
// state where Disconnect is enabled (only one message ever fires), so
// a wrong-target mutation on Disconnect goes uncaught. Under
// bounds.maxInFlight: 2 TLC reaches the post-Disconnect state and
// the mutation falls out as a temporal-property violation.
//
// Expected results (after the #78 fix):
//   low-bounds-correct   → PASS  (no mutation, low bounds)
//   low-bounds-mutated   → PASS  (mutation present but unreachable: false negative)
//   high-bounds-correct  → PASS  (no mutation, high bounds: ensures holds)
//   high-bounds-mutated  → FAIL  (mutation reachable, ensures violated)
//
// The two interesting rows are the low-bounds-mutated false negative
// (proves the gap exists without the fix) and the high-bounds-mutated
// failure (proves the fix closes the gap).
//
// Requires Docker + the polly-tla:latest image to be available locally.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { generateSubsystemTLA } from "../tools/verify/src/codegen/tla";
import { DockerRunner } from "../tools/verify/src/runner/docker";
import type {
  CodebaseAnalysis,
  MessageHandler,
  SubsystemConfig,
  VerificationConfig,
} from "../tools/verify/src/types";

const MESSAGE_ROUTER_TLA = path.join(
  __dirname,
  "..",
  "tools",
  "verify",
  "specs",
  "tla",
  "MessageRouter.tla"
);

type Outcome = "passed" | "ensures-violated" | "other-failure";

function makeHandler(
  messageType: string,
  assignments: Array<{ field: string; value: string }>,
  opts: { precondition?: string; postcondition?: string } = {}
): MessageHandler {
  return {
    messageType,
    node: "background",
    assignments,
    preconditions: opts.precondition
      ? [{ expression: opts.precondition, message: "", location: { line: 1, column: 1 } }]
      : [],
    postconditions: opts.postcondition
      ? [{ expression: opts.postcondition, message: "", location: { line: 1, column: 1 } }]
      : [],
    location: { file: "scripts/verify-issue-78.ts", line: 1 },
  };
}

function buildAnalysis(opts: { mutateDisconnect: boolean }): CodebaseAnalysis {
  const disconnectAssignment = opts.mutateDisconnect
    ? { field: "phase", value: "connected" } // wrong-target: violates the ensures
    : { field: "phase", value: "disconnected" };
  return {
    stateType: null,
    messageTypes: ["Connect", "Disconnect"],
    fields: [],
    handlers: [
      makeHandler("Connect", [{ field: "phase", value: "connected" }]),
      makeHandler("Disconnect", [disconnectAssignment], {
        precondition: "state.phase === 'connected'",
        postcondition: "state.phase === 'disconnected'",
      }),
    ],
    stateConstraints: [],
  };
}

function buildConfig(): VerificationConfig {
  return {
    state: {
      phase: {
        type: "enum",
        values: ["disconnected", "connected"],
      },
    },
    messages: { maxInFlight: 1, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
  };
}

const baseSubsystem: Omit<SubsystemConfig, "bounds"> = {
  state: ["phase"],
  handlers: ["Connect", "Disconnect"],
};

function classify(output: string, success: boolean): Outcome {
  if (success) return "passed";
  const propertyViolated =
    output.includes("Temporal properties were violated") ||
    output.includes("EnsuresAfter_HandleDisconnect") ||
    output.includes("Error: Invariant EnsuresAfter_");
  if (propertyViolated) return "ensures-violated";
  return "other-failure";
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

async function runOne(
  docker: DockerRunner,
  label: string,
  maxInFlight: number,
  mutate: boolean
): Promise<{ outcome: Outcome; tmpDir: string; output: string }> {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), `polly-i78-${label}-`));
  const config = buildConfig();
  const analysis = buildAnalysis({ mutateDisconnect: mutate });
  // Cap each message type at 1 occurrence — the connection state machine
  // is monotonic (each handler fires at most once on a given path), so
  // anything more is wasted exploration.
  const subsystem: SubsystemConfig = {
    ...baseSubsystem,
    bounds: {
      maxInFlight,
      perMessageBounds: { Connect: 1, Disconnect: 1 },
    },
  };

  const { spec, cfg } = await generateSubsystemTLA("connection", subsystem, config, analysis);
  const specPath = path.join(tmpDir, "UserApp_connection.tla");
  fs.writeFileSync(specPath, spec);
  fs.writeFileSync(path.join(tmpDir, "UserApp_connection.cfg"), cfg);
  fs.copyFileSync(MESSAGE_ROUTER_TLA, path.join(tmpDir, "MessageRouter.tla"));

  const result = await docker.runTLC(specPath, { workers: 1, timeout: 300_000 });
  return {
    outcome: classify(result.output ?? "", result.success === true),
    tmpDir,
    output: result.output ?? "",
  };
}

async function main(): Promise<void> {
  const docker = new DockerRunner();
  await ensurePrerequisites(docker);

  console.log("Issue #78 e2e: per-subsystem bounds reach multi-step ensures\n");

  type Case = {
    label: string;
    maxInFlight: number;
    mutate: boolean;
    expected: Outcome;
    rationale: string;
  };
  const cases: Case[] = [
    {
      label: "low-bounds-correct",
      maxInFlight: 1,
      mutate: false,
      expected: "passed",
      rationale: "no mutation, low bounds",
    },
    {
      label: "low-bounds-mutated",
      maxInFlight: 1,
      mutate: true,
      expected: "passed",
      rationale: "mutation present but Disconnect unreachable: false negative",
    },
    {
      label: "high-bounds-correct",
      maxInFlight: 2,
      mutate: false,
      expected: "passed",
      rationale: "no mutation, high bounds: ensures holds",
    },
    {
      label: "high-bounds-mutated",
      maxInFlight: 2,
      mutate: true,
      expected: "ensures-violated",
      rationale: "mutation reachable: ensures must fail",
    },
  ];

  const failedDirs: string[] = [];
  let allOk = true;
  for (const c of cases) {
    process.stdout.write(`▸ ${c.label.padEnd(22)} `);
    const start = Date.now();
    const { outcome, tmpDir, output } = await runOne(docker, c.label, c.maxInFlight, c.mutate);
    const elapsed = ((Date.now() - start) / 1000).toFixed(1);
    const ok = outcome === c.expected;
    if (!ok) allOk = false;
    console.log(`${ok ? "OK" : "MISMATCH"}  ${outcome.padEnd(20)} (${elapsed}s)  — ${c.rationale}`);
    if (ok) {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } else {
      const logPath = path.join(tmpDir, "tlc-output.log");
      fs.writeFileSync(logPath, output);
      console.log(`   ↳ output: ${logPath}`);
      failedDirs.push(tmpDir);
    }
  }

  console.log();
  if (allOk) {
    console.log(
      "Issue #78 verification PASSED — bounds.maxInFlight changes which ensures TLC evaluates."
    );
    return;
  }
  console.log("Issue #78 verification FAILED.");
  if (failedDirs.length > 0) {
    console.log(`  artefacts kept: ${failedDirs.join(", ")}`);
  }
  process.exit(1);
}

main().catch((err) => {
  console.log(err);
  process.exit(1);
});
