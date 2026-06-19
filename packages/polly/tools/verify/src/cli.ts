#!/usr/bin/env bun
// CLI for verification system

import * as fs from "node:fs";
import * as path from "node:path";
import { type ValidationResult, validateExpressions } from "./analysis/expression-validator";
import { computeMeshOrPeerSignalFindings } from "./analysis/mesh-signal-warnings";
import {
  estimateStateSpace,
  feasibilityLabel,
  type StateSpaceEstimate,
} from "./analysis/state-space-estimator";
import { generateConfig } from "./codegen/config";
import { validateConfig } from "./config/parser";
import type { UnifiedVerificationConfig } from "./config/types";
import { analyzeCodebase } from "./extract/types";
import { isSeedFixDisabled, meshSeedCfg } from "./runner/mesh-seed";

const COLORS = {
  reset: "\x1b[0m",
  red: "\x1b[31m",
  green: "\x1b[32m",
  yellow: "\x1b[33m",
  blue: "\x1b[34m",
  gray: "\x1b[90m",
};

function color(text: string, colorCode: string): string {
  return `${colorCode}${text}${COLORS.reset}`;
}

async function main() {
  const args = process.argv.slice(2);
  const command = args[0];

  switch (command) {
    case "--setup":
    case "setup":
      await setupCommand();
      break;

    case "--validate":
    case "validate":
      await validateCommand();
      break;

    case "--estimate":
    case "estimate":
      await estimateCommand();
      break;

    case "--help":
    case "help":
      showHelp();
      break;

    default:
      await verifyCommand();
  }
}

async function setupCommand() {
  console.log(color("\n🔍 Analyzing codebase...\n", COLORS.blue));

  try {
    // Find tsconfig
    const tsConfigPath = findTsConfig();
    if (!tsConfigPath) {
      process.exit(1);
    }

    console.log(color(`   Using: ${tsConfigPath}`, COLORS.gray));

    // Analyze codebase
    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: findStateFile(),
    });

    displayAnalysisResults(analysis);
    displayAnalysisSummary(analysis);

    // Generate and write config
    const configContent = generateConfig(analysis);
    const configPath = path.join(process.cwd(), "specs", "verification.config.ts");

    writeConfigFile(configPath, configContent);
    displaySetupSuccess(configPath);
  } catch (_error) {
    process.exit(1);
  }
}

function displayAnalysisResults(analysis: {
  stateType?: unknown;
  fields: unknown[];
  messageTypes: unknown[];
}): void {
  if (analysis.stateType) {
    console.log(color(`✓ Found state type with ${analysis.fields.length} field(s)`, COLORS.green));
  } else {
    console.log(color("\n⚠️  Could not find state type definition", COLORS.yellow));
    console.log("   Expected to find a type named 'AppState' or 'State'");
    console.log("   in a file matching **/state*.ts");
    console.log();
    console.log("   You can still generate a config template:");
    console.log("   It will be empty and you'll need to fill it in manually.");
    console.log();
  }

  console.log(color(`✓ Found ${analysis.messageTypes.length} message type(s)`, COLORS.green));
}

function displayAnalysisSummary(analysis: {
  fields: Array<{ path: string; type: { kind: string }; confidence: string }>;
}): void {
  if (analysis.fields.length === 0) return;

  console.log(color("\n📊 Configuration Summary:\n", COLORS.blue));

  const table = [
    ["Field", "Type", "Status"],
    ["─".repeat(30), "─".repeat(20), "─".repeat(20)],
  ];

  for (const field of analysis.fields) {
    const status = getFieldStatus(field.confidence);
    table.push([field.path, field.type.kind, status]);
  }

  for (const row of table) {
    console.log(`   ${row[0]?.padEnd(32) ?? ""} ${row[1]?.padEnd(22) ?? ""} ${row[2] ?? ""}`);
  }
}

function getFieldStatus(confidence: string): string {
  if (confidence === "high") return color("✓ Auto-configured", COLORS.green);
  if (confidence === "medium") return color("⚠ Review needed", COLORS.yellow);
  return color("⚠ Manual config", COLORS.red);
}

function writeConfigFile(configPath: string, configContent: string): void {
  const configDir = path.dirname(configPath);
  if (!fs.existsSync(configDir)) {
    fs.mkdirSync(configDir, { recursive: true });
  }
  fs.writeFileSync(configPath, configContent, "utf-8");
}

function displaySetupSuccess(configPath: string): void {
  console.log(color("\n✅ Configuration generated!\n", COLORS.green));
  console.log(`   File: ${color(configPath, COLORS.blue)}`);
  console.log();
  console.log(color("📝 Next steps:", COLORS.blue));
  console.log();
  console.log("   1. Review the generated configuration file");
  console.log("   2. Fill in values marked with /* CONFIGURE */");
  console.log("   3. Run 'polly verify' to check your configuration");
  console.log();
  console.log(color("💡 Tip:", COLORS.gray));
  console.log(color("   Look for comments explaining what each field needs.", COLORS.gray));
  console.log();
}

async function validateCommand() {
  const configPath = path.join(process.cwd(), "specs", "verification.config.ts");

  console.log(color("\n🔍 Validating configuration...\n", COLORS.blue));

  const result = validateConfig(configPath);

  if (result.valid) {
    console.log(color("✅ Configuration is complete and valid!\n", COLORS.green));
    console.log("   You can now run 'polly verify' to start verification.");
    console.log();
    return;
  }

  // Show errors
  const errors = result.issues.filter((i) => i.severity === "error");
  const warnings = result.issues.filter((i) => i.severity === "warning");

  displayValidationErrors(errors);
  displayValidationWarnings(warnings);

  console.log(color("Configuration incomplete. Please fix the errors above.\n", COLORS.red));
  process.exit(1);
}

async function estimateCommand() {
  const configPath = path.join(process.cwd(), "specs", "verification.config.ts");

  console.log(color("\n📊 Estimating state space...\n", COLORS.blue));

  // Validate config first
  const validation = validateConfig(configPath);
  if (!validation.valid) {
    const errors = validation.issues.filter((i) => i.severity === "error");
    console.log(color(`❌ Configuration incomplete (${errors.length} error(s))\n`, COLORS.red));
    for (const error of errors.slice(0, 3)) {
      console.log(color(`   • ${error.message}`, COLORS.red));
    }
    console.log("\n   Run 'polly verify --validate' to see all issues");
    process.exit(1);
  }

  // Load config
  const config = await loadVerificationConfig(configPath);

  // Analyze codebase
  const analysis = await runCodebaseAnalysis();

  // Validate expressions
  const typedConfig = config as unknown as import("./config/types").UnifiedVerificationConfig;
  const typedAnalysis = analysis as unknown as import("./core/model").CodebaseAnalysis;
  const meshSignalNames = new Set(
    (typedAnalysis.meshOrPeerSignals ?? []).map((s) => s.variableName)
  );
  const exprValidation = validateExpressions(
    typedAnalysis.handlers,
    typedConfig.state,
    meshSignalNames
  );
  if (exprValidation.warnings.length > 0) {
    displayExpressionWarnings(exprValidation);
  }

  // Estimate
  const estimate = estimateStateSpace(typedConfig, typedAnalysis);

  displayEstimate(estimate);
}

function displayEstimate(estimate: StateSpaceEstimate): void {
  console.log(color("State space estimate:\n", COLORS.blue));

  // Fields table
  console.log(color("  Fields:", COLORS.blue));
  for (const field of estimate.fields) {
    const name = field.name.padEnd(28);
    const kind = field.kind.padEnd(18);
    const card =
      field.cardinality === "unbounded"
        ? color("(excluded — unbounded)", COLORS.yellow)
        : `${field.cardinality} values`;
    console.log(`    ${name} ${kind} ${card}`);
  }

  console.log();
  console.log(`  Field combinations:     ${color(String(estimate.fieldProduct), COLORS.green)}`);
  console.log(`  Handlers:               ${estimate.handlerCount}`);
  console.log(`  Max in-flight:          ${estimate.maxInFlight}`);
  console.log(
    `  Contexts:               ${estimate.contextCount} (${estimate.contextCount - 1} tab${estimate.contextCount - 1 === 1 ? "" : "s"} + background)`
  );
  console.log(`  Interleaving factor:    ${estimate.interleavingFactor}`);

  console.log();
  console.log(
    `  Estimated states:       ${color(`~${estimate.estimatedStates.toLocaleString()}`, COLORS.green)}`
  );

  // Feasibility
  const feasColor =
    estimate.feasibility === "trivial" || estimate.feasibility === "feasible"
      ? COLORS.green
      : estimate.feasibility === "slow"
        ? COLORS.yellow
        : COLORS.red;
  console.log();
  console.log(`  Assessment: ${color(feasibilityLabel(estimate.feasibility), feasColor)}`);

  // Warnings
  if (estimate.warnings.length > 0) {
    console.log();
    for (const w of estimate.warnings) {
      console.log(color(`  ⚠️  ${w}`, COLORS.yellow));
    }
  }

  // Suggestions
  if (estimate.suggestions.length > 0) {
    console.log();
    console.log(color("  Suggestions:", COLORS.blue));
    for (const s of estimate.suggestions) {
      console.log(color(`    • ${s}`, COLORS.gray));
    }
  }

  console.log();
}

function displayValidationErrors(
  errors: Array<{
    message: string;
    field?: string;
    location?: { line: number };
    suggestion: string;
  }>
): void {
  if (errors.length === 0) return;

  console.log(color(`❌ Found ${errors.length} error(s):\n`, COLORS.red));

  for (const error of errors) {
    console.log(color(`   • ${error.message}`, COLORS.red));
    if (error.field) {
      console.log(color(`     Field: ${error.field}`, COLORS.gray));
    }
    if (error.location) {
      console.log(color(`     Location: line ${error.location.line}`, COLORS.gray));
    }
    console.log(color(`     → ${error.suggestion}`, COLORS.yellow));
    console.log();
  }
}

function displayValidationWarnings(
  warnings: Array<{ message: string; field?: string; suggestion: string }>
): void {
  if (warnings.length === 0) return;

  console.log(color(`⚠️  Found ${warnings.length} warning(s):\n`, COLORS.yellow));

  for (const warning of warnings) {
    console.log(color(`   • ${warning.message}`, COLORS.yellow));
    if (warning.field) {
      console.log(color(`     Field: ${warning.field}`, COLORS.gray));
    }
    console.log(color(`     → ${warning.suggestion}`, COLORS.gray));
    console.log();
  }
}

function displayExpressionWarnings(result: ValidationResult): void {
  if (result.warnings.length === 0) return;

  console.log(color(`⚠️  Found ${result.warnCount} expression warning(s):\n`, COLORS.yellow));

  for (const w of result.warnings) {
    console.log(color(`   ⚠  ${w.message}`, COLORS.yellow));
    console.log(color(`      ${w.expression}`, COLORS.gray));
    console.log(color(`      at ${w.location.file}:${w.location.line}`, COLORS.gray));
    console.log(color(`      → ${w.suggestion}`, COLORS.yellow));
    console.log();
  }
}

/**
 * polly#117: warn when a handler's requires/ensures predicate
 * references a `$meshState`/`$peerState` signal whose cross-peer
 * semantics the verifier does NOT check.
 *
 * A `$meshState` document declared under `mesh:` in the verification
 * config is routed through the `meshState` namespace with a
 * `PropagateMeshOp` action — its cross-peer claims are genuinely
 * checked, so it is NOT warned about. An *undeclared* `$meshState`
 * signal, or any `$peerState` signal, is flattened to single-context
 * local state; a predicate over it silently asserts only the
 * executing context's view. This warning makes that narrowing loud
 * and points at the fix.
 */
function displayMeshOrPeerSignalWarnings(
  analysis: import("./core/model").CodebaseAnalysis,
  declaredMeshDocs: ReadonlySet<string>
): number {
  const findings = computeMeshOrPeerSignalFindings(analysis, declaredMeshDocs);
  if (findings.length === 0) return 0;

  const hasUndeclaredMesh = findings.some((f) => f.signalKind === "mesh");
  const hasPeer = findings.some((f) => f.signalKind === "peer");

  console.log(
    color(
      `\n⚠️  ${findings.length} predicate(s) reference an unverified $meshState/$peerState signal (polly#117):`,
      COLORS.yellow
    )
  );
  console.log(
    color(
      "   These signals are flattened to single-context local state, so a green run",
      COLORS.gray
    )
  );
  console.log(color("   does NOT prove the claim holds across peers.", COLORS.gray));
  if (hasUndeclaredMesh) {
    console.log(
      color(
        "   Fix ($meshState): declare the document key under `mesh: { ... }` in your",
        COLORS.gray
      )
    );
    console.log(
      color(
        "   verification config. Declared mesh docs are routed through the meshState",
        COLORS.gray
      )
    );
    console.log(
      color(
        "   namespace with a PropagateMeshOp action, so `forAllPeers(...)` claims are checked.",
        COLORS.gray
      )
    );
  }
  if (hasPeer) {
    console.log(
      color("   $peerState signals have no cross-peer verification model yet.", COLORS.gray)
    );
  }
  console.log();

  for (const f of findings) {
    const remedy =
      f.signalKind === "mesh" ? "not declared in config.mesh" : "$peerState — no cross-peer model";
    console.log(color(`   ⚠  ${f.handler} ${f.kind}: ${f.signalName} (${remedy})`, COLORS.yellow));
    console.log(color(`      ${f.expression}`, COLORS.gray));
    console.log(color(`      at ${f.location.file}:${f.location.line}`, COLORS.gray));
    console.log();
  }

  return findings.length;
}

/**
 * polly#160 (Ask #1): does the operator want a fail-closed run? `--strict`
 * (or POLLY_VERIFY_STRICT=1) turns model-coverage gaps and unverified
 * mesh/peer signals from warnings into a non-zero exit, so a silently
 * unmodelled path cannot pass with a green check.
 */
function isStrictMode(): boolean {
  return process.argv.includes("--strict") || process.env.POLLY_VERIFY_STRICT === "1";
}

/**
 * `polly verify --witness`: after the invariant pass, turn each BDD scenario's
 * Then-predicate into a per-scenario TLC reachability check (the deeper BDD ↔
 * verify link). A scenario whose outcome the exhaustive model proves
 * unreachable is a scenario that lies. Off by default — it adds one TLC run per
 * witnessable scenario.
 */
function isWitnessMode(): boolean {
  return process.argv.includes("--witness");
}

/**
 * polly#160 (Ask #1): render the model-coverage report — which declared state
 * fields are written by which handlers, which are written by none, and which
 * mutators pin no postcondition. Clean specs get a one-line confirmation.
 */
function displayModelCoverage(
  report: import("./analysis/model-coverage").ModelCoverageReport
): void {
  const { unwrittenFields, unconstrainedMutators, fieldCoverage } = report;

  if (unwrittenFields.length === 0 && unconstrainedMutators.length === 0) {
    console.log(
      color(
        `✓ Model coverage: all ${fieldCoverage.length} declared field(s) written by a modelled handler`,
        COLORS.green
      )
    );
    console.log();
    return;
  }

  if (unwrittenFields.length > 0) {
    console.log(
      color(
        `\n⚠️  ${unwrittenFields.length} declared state field(s) written by NO modelled handler (polly#160):`,
        COLORS.yellow
      )
    );
    for (const f of unwrittenFields) {
      console.log(color(`   • ${f}`, COLORS.yellow));
    }
    console.log(
      color(
        "   The model carries a variable no transition can change. Either it is dead",
        COLORS.gray
      )
    );
    console.log(
      color(
        "   state (drop it from the verified surface) or its mutating path was never",
        COLORS.gray
      )
    );
    console.log(
      color("   modelled — the omission class both TLC and mutation testing miss.", COLORS.gray)
    );
    console.log();
  }

  if (unconstrainedMutators.length > 0) {
    console.log(
      color(
        `ℹ️  ${unconstrainedMutators.length} handler(s) mutate declared state with no ensures() postcondition:`,
        COLORS.gray
      )
    );
    for (const m of unconstrainedMutators) {
      console.log(
        color(
          `   • ${m.handler} writes {${m.fields.join(", ")}} — ${m.location.file}:${m.location.line}`,
          COLORS.gray
        )
      );
    }
    console.log(
      color(
        "   The checker explores these transitions but asserts nothing about their effect.",
        COLORS.gray
      )
    );
    console.log();
  }
}

/**
 * polly#160 (Ask #1): compute and render the model-coverage report, then —
 * under --strict — fail closed before the expensive TLC pass when the model
 * has an unwritten declared field or an unverified mesh/peer signal. Extracted
 * from runFullVerification to keep that orchestrator within complexity limits.
 */
async function runModelCoverage(
  typedConfig: UnifiedVerificationConfig,
  typedAnalysis: import("./core/model").CodebaseAnalysis,
  meshFindingCount: number
): Promise<void> {
  const { computeModelCoverage, strictCoverageReasons } = await import("./analysis/model-coverage");
  const stateFields = Object.keys(typedConfig.state ?? {});
  const coverage = computeModelCoverage(stateFields, typedAnalysis.handlers);
  displayModelCoverage(coverage);

  if (!isStrictMode()) return;

  const reasons = strictCoverageReasons(coverage, meshFindingCount);

  if (reasons.length === 0) {
    console.log(color("✓ Strict mode: model coverage complete", COLORS.green));
    console.log();
    return;
  }

  console.log(color("❌ Strict mode: model coverage incomplete\n", COLORS.red));
  for (const reason of reasons) {
    console.log(color(`   • ${reason}`, COLORS.red));
  }
  console.log();
  console.log(
    color("   --strict fails closed on these so an unmodelled path cannot pass with a", COLORS.gray)
  );
  console.log(
    color("   green check. Re-run without --strict to treat them as warnings.", COLORS.gray)
  );
  console.log();
  process.exit(1);
}

async function verifyCommand() {
  const configPath = path.join(process.cwd(), "specs", "verification.config.ts");

  console.log(color("\n🔍 Running verification...\n", COLORS.blue));

  // First validate config
  const validation = validateConfig(configPath);

  if (!validation.valid) {
    const errors = validation.issues.filter((i) => i.severity === "error");
    console.log(color(`❌ Configuration incomplete (${errors.length} error(s))\n`, COLORS.red));

    for (const error of errors.slice(0, 3)) {
      console.log(color(`   • ${error.message}`, COLORS.red));
      if (error.field) {
        console.log(color(`     Field: ${error.field}`, COLORS.gray));
      }
      console.log();
    }

    if (errors.length > 3) {
      console.log(color(`   ... and ${errors.length - 3} more error(s)`, COLORS.gray));
      console.log();
    }

    console.log("   Run 'polly verify --validate' to see all issues");
    console.log("   Run 'polly verify --setup' to regenerate configuration");
    console.log();
    process.exit(1);
  }

  console.log(color("✓ Configuration valid", COLORS.green));
  console.log();

  // Run full verification
  try {
    await runFullVerification(configPath);
  } catch (error) {
    // biome-ignore lint/suspicious/noConsole: CLI tool needs console output for error reporting
    console.error(color("\n❌ Verification error:", COLORS.red));
    if (error instanceof Error) {
      // biome-ignore lint/suspicious/noConsole: CLI tool needs console output for error reporting
      console.error(color(error.message, COLORS.red));
      if (process.env.POLLY_DEBUG) {
        // biome-ignore lint/suspicious/noConsole: CLI tool needs console output for error reporting
        console.error(color("\nStack trace:", COLORS.gray));
        // biome-ignore lint/suspicious/noConsole: CLI tool needs console output for error reporting
        console.error(error.stack);
      }
    } else {
      // biome-ignore lint/suspicious/noConsole: CLI tool needs console output for error reporting
      console.error(String(error));
    }
    // biome-ignore lint/suspicious/noConsole: CLI tool needs console output for error reporting
    console.error();
    process.exit(1);
  }
}

/**
 * polly#117/#114: read the docIds of the optional `mesh` record off a loaded
 * config without asserting its shape.
 */
function getMeshDocIds(config: unknown): string[] {
  if (typeof config !== "object" || config === null || !("mesh" in config)) return [];
  const mesh = config.mesh;
  if (typeof mesh !== "object" || mesh === null) return [];
  return Object.keys(mesh);
}

/**
 * Get timeout in seconds from config (0 = no timeout)
 */
function getTimeout(config: UnifiedVerificationConfig): number {
  return config.verification?.timeout ?? 0;
}

/**
 * Get number of workers from config
 */
function getWorkers(config: UnifiedVerificationConfig): number {
  return config.verification?.workers ?? 1;
}

/**
 * Get maxDepth from config for bounded model checking (Tier 2)
 */
function getMaxDepth(config: UnifiedVerificationConfig): number | undefined {
  // maxDepth is only available in legacy config format with tier2 settings
  if ("tier2" in config && config.tier2?.boundedExploration?.maxDepth) {
    return config.tier2.boundedExploration.maxDepth;
  }
  return undefined;
}

/**
 * polly#160 (A2): coupled-field write-coupling lint. WARNS only — a legitimate
 * staged transition (one handler sets each field) trips the per-handler subset
 * check, so this never fails the run. The sound, whole-state detector is the
 * `capabilities` TLA+ invariant. Runs in runFullVerification before the
 * subsystem/monolithic branch, so it covers both paths.
 */
async function runCoupledFieldsLint(
  config: UnifiedVerificationConfig,
  analysis: import("./core/model").CodebaseAnalysis
): Promise<void> {
  const groups = config.coupledFields ?? [];
  if (groups.length === 0) return;

  const { checkCoupledFields } = await import("./analysis/coupled-fields");
  const result = checkCoupledFields(groups, analysis.handlers);

  if (result.valid) {
    console.log(color("✓ Coupled fields: verified (no partial-subset writes)", COLORS.green));
    console.log();
    return;
  }

  console.log(color("⚠️  Coupled-field violations detected:\n", COLORS.yellow));
  for (const v of result.violations) {
    console.log(
      color(
        `   • Handler "${v.handler}" writes {${v.written.join(", ")}} but not {${v.missing.join(
          ", "
        )}} of coupled group {${v.group.join(", ")}}`,
        COLORS.yellow
      )
    );
  }
  console.log();
  console.log(
    color(
      "   These fields are declared to move together; a capability granted without its",
      COLORS.yellow
    )
  );
  console.log(
    color(
      "   precondition is a likely cause. Co-write the full group in each handler, or model",
      COLORS.yellow
    )
  );
  console.log(color("   the relationship with a `capabilities` invariant.", COLORS.yellow));
  console.log();
}

async function runFullVerification(configPath: string) {
  // Load config
  const config = await loadVerificationConfig(configPath);

  // Analyze codebase
  const analysis = await runCodebaseAnalysis();

  // Validate expressions
  const typedConfig = config as unknown as UnifiedVerificationConfig;
  const typedAnalysis = analysis as unknown as import("./core/model").CodebaseAnalysis;
  // polly#117: mesh/peer signal variable names — references into these
  // are not "unmodeled fields"; they are handled by the dedicated
  // mesh/peer signal warning below.
  const meshSignalNames = new Set(
    (typedAnalysis.meshOrPeerSignals ?? []).map((s) => s.variableName)
  );
  const exprValidation = validateExpressions(
    typedAnalysis.handlers,
    typedConfig.state,
    meshSignalNames
  );
  if (exprValidation.warnings.length > 0) {
    displayExpressionWarnings(exprValidation);
  }

  // polly#117: surface mesh- and peer-scoped signal references whose
  // cross-peer semantics the codegen does not check. A $meshState doc
  // declared under `mesh:` is verified cross-peer and excluded.
  const declaredMeshDocs = new Set(getMeshDocIds(typedConfig));
  const meshFindingCount = displayMeshOrPeerSignalWarnings(typedAnalysis, declaredMeshDocs);

  // polly#160: coupled-field write-coupling lint (warn-only). One call here
  // covers both the subsystem and monolithic paths below.
  await runCoupledFieldsLint(typedConfig, typedAnalysis);

  // polly#160 (Ask #1): model-coverage report + optional fail-closed gate.
  await runModelCoverage(typedConfig, typedAnalysis, meshFindingCount);

  // Check for subsystem-scoped verification
  if (typedConfig.subsystems && Object.keys(typedConfig.subsystems).length > 0) {
    await runSubsystemVerification(typedConfig, typedAnalysis);
    if (isWitnessMode()) {
      await runWitnessVerification(typedConfig);
    }
    return;
  }

  // Monolithic verification (fallback)
  await runMonolithicVerification(config, analysis);
  if (isWitnessMode()) {
    console.log(
      color(
        "\n⚠ --witness needs subsystem-scoped verification (a `subsystems` block in the config);",
        COLORS.yellow
      )
    );
    console.log(
      color("  reachability witnesses route each scenario to its subsystem spec.\n", COLORS.yellow)
    );
  }
}

async function runMonolithicVerification(config: unknown, analysis: unknown) {
  // Generate TLA+ specs
  const { specPath, specDir } = await generateAndWriteTLASpecs(config, analysis);

  // Find and copy base spec
  findAndCopyBaseSpec(specDir);

  console.log(color("✓ Specification generated", COLORS.green));
  console.log(color(`   ${specPath}`, COLORS.gray));
  console.log();

  // Setup and run Docker
  const docker = await setupDocker();

  // Determine timeout, workers, and maxDepth from config
  const typedConfig = config as unknown as UnifiedVerificationConfig;
  const timeoutSeconds = getTimeout(typedConfig);
  const workers = getWorkers(typedConfig);
  const maxDepth = getMaxDepth(typedConfig);

  // Run TLC
  console.log(color("⚙️  Running TLC model checker...", COLORS.blue));
  if (timeoutSeconds === 0) {
    console.log(color("   No timeout set - will run until completion", COLORS.gray));
  } else {
    const timeoutMinutes = Math.floor(timeoutSeconds / 60);
    const timeoutLabel =
      timeoutMinutes > 0
        ? `${timeoutMinutes} minute${timeoutMinutes > 1 ? "s" : ""}`
        : `${timeoutSeconds} seconds`;
    console.log(color(`   Timeout: ${timeoutLabel}`, COLORS.gray));
  }
  if (maxDepth !== undefined) {
    console.log(color(`   Max depth: ${maxDepth}`, COLORS.gray));
  }
  console.log();

  const result = await docker.runTLC(specPath, {
    workers,
    timeout: timeoutSeconds > 0 ? timeoutSeconds * 1000 : undefined,
    maxDepth,
  });

  // polly#114: when the project declares $meshState documents, also
  // model-check the concurrent first-time seed — the polly#113 race that
  // lived entirely outside verification. A failure here is reported and
  // exits before the project-spec result.
  const meshSeed = await runMeshSeedGuard(docker, specDir, config);
  if (meshSeed && !meshSeed.success) {
    console.log(color("\n❌ Mesh seed-race guard failed (polly#113 / polly#114)\n", COLORS.red));
    displayVerificationResults(meshSeed, specDir);
  }
  if (meshSeed) {
    console.log(color("✓ Mesh seed-race guard passed (MeshSeed.tla)\n", COLORS.green));
  }

  // Display results
  displayVerificationResults(result, specDir);
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Subsystem orchestration requires sequential steps with branching
async function runSubsystemVerification(
  config: UnifiedVerificationConfig,
  analysis: import("./core/model").CodebaseAnalysis
) {
  const subsystems = config.subsystems as unknown as Record<
    string,
    { state: string[]; handlers: string[] }
  >;
  const subsystemNames = Object.keys(subsystems);

  console.log(
    color(`Subsystem-scoped verification (${subsystemNames.length} subsystems)\n`, COLORS.blue)
  );

  // Non-interference check
  const { checkNonInterference } = await import("./analysis/non-interference");
  const interference = checkNonInterference(subsystems, analysis.handlers);

  if (interference.valid) {
    console.log(
      color("✓ Non-interference: verified (no cross-subsystem state writes)", COLORS.green)
    );
    console.log();
  } else {
    console.log(color("⚠️  Non-interference violations detected:\n", COLORS.yellow));
    for (const v of interference.violations) {
      console.log(
        color(
          `   • Handler "${v.handler}" (${v.subsystem}) writes to "${v.writesTo}" owned by "${v.ownedBy}"`,
          COLORS.yellow
        )
      );
    }
    console.log();
    console.log(
      color(
        "   Compositional verification may not be sound. Consider restructuring subsystem boundaries.",
        COLORS.yellow
      )
    );
    console.log();
  }

  // Precondition-locality check (read-side complement to non-interference).
  // A handler whose requires() reads state owned by another subsystem will
  // silently never have its postcondition evaluated under compositional
  // verification: the foreign subsystem is absent during this pass, so the
  // pre-state the handler waits for is never produced and TLC reports PASS
  // without firing the property the user wrote.
  const { checkPreconditionLocality } = await import("./analysis/precondition-locality");
  const locality = checkPreconditionLocality(subsystems, analysis.handlers);

  if (locality.valid) {
    console.log(
      color("✓ Precondition locality: verified (no cross-subsystem requires() reads)", COLORS.green)
    );
    console.log();
  } else {
    console.log(color("⚠️  Precondition-locality violations detected:\n", COLORS.yellow));
    for (const v of locality.violations) {
      console.log(
        color(
          `   • Handler "${v.handler}" (${v.subsystem}) requires "${v.readsFrom}" owned by "${v.ownedBy}"`,
          COLORS.yellow
        )
      );
      console.log(color(`     ${v.expression}`, COLORS.gray));
    }
    console.log();
    console.log(
      color(
        "   Compositional verification of these subsystems cannot satisfy the precondition;",
        COLORS.yellow
      )
    );
    console.log(
      color(
        "   the handler's ensures() postcondition will not be evaluated. Consider restructuring",
        COLORS.yellow
      )
    );
    console.log(color("   subsystems to keep preconditions local.", COLORS.yellow));
    console.log();
  }

  // Warn about unassigned handlers
  const assignedHandlers = new Set(Object.values(subsystems).flatMap((s) => s.handlers));
  const unassigned = analysis.messageTypes.filter((mt) => !assignedHandlers.has(mt));
  if (unassigned.length > 0) {
    console.log(
      color(
        `⚠️  ${unassigned.length} handler(s) not assigned to any subsystem (will not be verified):`,
        COLORS.yellow
      )
    );
    for (const h of unassigned.slice(0, 10)) {
      console.log(color(`   • ${h}`, COLORS.yellow));
    }
    if (unassigned.length > 10) {
      console.log(color(`   ... and ${unassigned.length - 10} more`, COLORS.yellow));
    }
    console.log();
  }

  // Setup Docker once
  const docker = await setupDocker();
  const timeoutSeconds = getTimeout(config);
  const workers = getWorkers(config);
  const maxDepth = getMaxDepth(config);

  // Generate and run per-subsystem
  const { generateSubsystemTLA } = await import("./codegen/tla");
  const results: Array<{
    name: string;
    success: boolean;
    handlerCount: number;
    ensuresCount: number;
    stateCount: number;
    elapsed: number;
    stats?: { statesGenerated: number; distinctStates: number };
    error?: string;
  }> = [];

  for (const name of subsystemNames) {
    const sub = subsystems[name];
    const startTime = Date.now();

    console.log(color(`⚙️  Verifying subsystem: ${name}...`, COLORS.blue));

    // Generate per-subsystem TLA+
    const { spec, cfg } = await generateSubsystemTLA(name, sub, config, analysis);

    // Count step-temporal ensures properties registered for this subsystem.
    // This is the upper bound on postconditions TLC will evaluate; a property
    // only fires when its handler is enabled at some reachable state, so the
    // count overstates true coverage when handlers are multi-step-reachable
    // and bounds.maxInFlight is too low to reach them.
    const ensuresCount = (spec.match(/^EnsuresAfter_\w+ ==/gm) ?? []).length;

    // Write specs
    const specDir = path.join(process.cwd(), "specs", "tla", "generated", name);
    if (!fs.existsSync(specDir)) {
      fs.mkdirSync(specDir, { recursive: true });
    }

    const specPath = path.join(specDir, `UserApp_${name}.tla`);
    const cfgPath = path.join(specDir, `UserApp_${name}.cfg`);
    fs.writeFileSync(specPath, spec);
    fs.writeFileSync(cfgPath, cfg);

    // Copy base spec
    findAndCopyBaseSpec(specDir);

    // Run TLC
    const result = await docker.runTLC(specPath, {
      workers,
      timeout: timeoutSeconds > 0 ? timeoutSeconds * 1000 : undefined,
      maxDepth,
    });

    const elapsed = (Date.now() - startTime) / 1000;

    results.push({
      name,
      success: result.success,
      handlerCount: sub.handlers.length,
      ensuresCount,
      stateCount: result.stats?.distinctStates ?? 0,
      elapsed,
      stats: result.stats,
      error: result.error,
    });

    if (result.success) {
      console.log(color(`   ✓ ${name} passed (${elapsed.toFixed(1)}s)`, COLORS.green));
    } else {
      console.log(color(`   ✗ ${name} failed`, COLORS.red));
      if (result.violation) {
        console.log(color(`     Invariant violated: ${result.violation.name}`, COLORS.red));
      } else if (result.error) {
        console.log(color(`     Error: ${result.error}`, COLORS.red));
      }
      // Write full output for debugging
      fs.writeFileSync(path.join(specDir, "tlc-output.log"), result.output);
    }
  }

  console.log();

  // Compositional report
  displayCompositionalReport(results, interference.valid);
}

/** A finite default cap so an unconstrained witness cannot hang the run. */
const DEFAULT_WITNESS_TIMEOUT_MS = 180_000;

type WitnessStatus = "reachable" | "unreachable" | "inconclusive" | "skipped" | "error";

interface WitnessResult {
  id: string;
  status: WitnessStatus;
  subsystem?: string;
  predicate?: string;
  note?: string;
}

/** Absolute paths matching `pattern` under `cwd`, sorted. */
async function globAbsolute(cwd: string, pattern: string): Promise<string[]> {
  const out: string[] = [];
  for await (const f of new Bun.Glob(pattern).scan({ cwd, absolute: true, onlyFiles: true })) {
    out.push(f);
  }
  return out.sort();
}

/**
 * `polly verify --witness`: the deeper BDD ↔ verify link. Each BDD scenario's
 * Then-predicate (reduced by tools/bdd) becomes a per-scenario TLC reachability
 * check over the subsystem spec the normal pass just generated.
 *
 * Semantics, inverted from a normal invariant: the witness `~(\E ctx : <Then>)`
 * is *violated* exactly when the model reaches the asserted outcome — so a
 * violation is GOOD (the scenario is honest; the counterexample is its path).
 * A clean full exploration means the outcome is unreachable — the scenario
 * lies, and the run fails. Witnesses run WITHOUT the depth bound: a "reachable"
 * verdict is sound at any bound, but "unreachable" is only sound under full
 * exploration (StateConstraint keeps the space finite). If TLC times out first,
 * the verdict is inconclusive — reported, never silently passed or failed.
 */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: a flat per-scenario classify loop — the branches are the verdict surface.
async function runWitnessVerification(config: UnifiedVerificationConfig): Promise<void> {
  console.log(color("Reachability witnesses (--witness)\n", COLORS.blue));

  const cwd = process.cwd();
  const featureFiles = await globAbsolute(cwd, "features/**/*.feature");
  const stepFiles = [
    ...new Set([
      ...(await globAbsolute(cwd, "features/**/*.steps.ts")),
      ...(await globAbsolute(cwd, "features/steps.ts")),
    ]),
  ];
  if (featureFiles.length === 0 || stepFiles.length === 0) {
    console.log(
      color("  No .feature files / step modules found — nothing to witness.\n", COLORS.gray)
    );
    return;
  }

  const { extractWitnesses } = await import("../../bdd/src/witness");
  const {
    bddPredicateToTLA,
    buildWitnessCfg,
    buildWitnessModule,
    routeWitness,
    WITNESS_INVARIANT,
  } = await import("./codegen/witness");

  const subsystems = config.subsystems as unknown as Record<string, { state: string[] }>;
  const witnesses = await extractWitnesses(featureFiles, stepFiles);

  const docker = await setupDocker();
  const timeoutSeconds = getTimeout(config);
  const timeout = timeoutSeconds > 0 ? timeoutSeconds * 1000 : DEFAULT_WITNESS_TIMEOUT_MS;
  const workers = getWorkers(config);

  const results: WitnessResult[] = [];
  let idx = 0;

  for (const w of witnesses) {
    const id = `${w.feature} › ${w.scenario}`;
    if (!w.predicate) {
      results.push({ id, status: "skipped", note: "no state-observable Then to witness" });
      continue;
    }
    const subsystem = routeWitness(w.fields, subsystems);
    if (!subsystem) {
      results.push({
        id,
        status: "skipped",
        note: `fields [${w.fields.join(", ")}] not owned by a single subsystem`,
      });
      continue;
    }

    const specDir = path.join(cwd, "specs", "tla", "generated", subsystem);
    const subsystemCfg = path.join(specDir, `UserApp_${subsystem}.cfg`);
    if (
      !fs.existsSync(path.join(specDir, `UserApp_${subsystem}.tla`)) ||
      !fs.existsSync(subsystemCfg)
    ) {
      results.push({
        id,
        status: "error",
        subsystem,
        note: `subsystem spec missing: ${subsystem}`,
      });
      continue;
    }

    let tlaPredicate: string;
    try {
      tlaPredicate = bddPredicateToTLA(w.predicate);
    } catch (err) {
      results.push({
        id,
        status: "error",
        subsystem,
        note: err instanceof Error ? err.message : String(err),
      });
      continue;
    }

    const moduleName = `Witness_${subsystem}_${idx++}`;
    const witnessTla = path.join(specDir, `${moduleName}.tla`);
    fs.writeFileSync(
      witnessTla,
      buildWitnessModule(moduleName, `UserApp_${subsystem}`, tlaPredicate)
    );
    fs.writeFileSync(
      path.join(specDir, `${moduleName}.cfg`),
      buildWitnessCfg(fs.readFileSync(subsystemCfg, "utf8"))
    );

    console.log(color(`⚙️  ${id}`, COLORS.blue));
    console.log(color(`     ${subsystem} ⊨ ${w.predicate}`, COLORS.gray));

    let tlc: Awaited<ReturnType<Awaited<ReturnType<typeof setupDocker>>["runTLC"]>>;
    try {
      tlc = await docker.runTLC(witnessTla, { workers, timeout });
    } catch (err) {
      const msg = err instanceof Error ? err.message : String(err);
      results.push({ id, status: "inconclusive", subsystem, predicate: w.predicate, note: msg });
      console.log(
        color("     ⚠ inconclusive — TLC did not finish (raise the config timeout)", COLORS.yellow)
      );
      continue;
    }

    if (!tlc.success && tlc.violation?.name === WITNESS_INVARIANT) {
      results.push({ id, status: "reachable", subsystem, predicate: w.predicate });
      console.log(color("     ✓ reachable — the model reaches this outcome", COLORS.green));
    } else if (tlc.success) {
      results.push({
        id,
        status: "unreachable",
        subsystem,
        predicate: w.predicate,
        note: `${tlc.stats?.distinctStates ?? 0} distinct states, no path`,
      });
      console.log(
        color(
          "     ✗ UNREACHABLE — the model proves this outcome impossible (the scenario lies)",
          COLORS.red
        )
      );
      fs.writeFileSync(path.join(specDir, `${moduleName}.tlc-output.log`), tlc.output);
    } else {
      results.push({
        id,
        status: "error",
        subsystem,
        predicate: w.predicate,
        note: tlc.error ?? tlc.violation?.name ?? "TLC error",
      });
      console.log(color(`     ! error — ${tlc.error ?? "see log"}`, COLORS.yellow));
      fs.writeFileSync(path.join(specDir, `${moduleName}.tlc-output.log`), tlc.output);
    }
  }

  displayWitnessReport(results);
}

function displayWitnessReport(results: WitnessResult[]): void {
  const count = (s: WitnessStatus) => results.filter((r) => r.status === s).length;
  const reachable = count("reachable");
  const unreachable = count("unreachable");
  const inconclusive = count("inconclusive");
  const errors = count("error");
  const skipped = count("skipped");

  console.log();
  console.log(color("Witness results:\n", COLORS.blue));
  for (const r of results) {
    const mark = {
      reachable: color("✓", COLORS.green),
      unreachable: color("✗", COLORS.red),
      inconclusive: color("⚠", COLORS.yellow),
      error: color("!", COLORS.yellow),
      skipped: color("·", COLORS.gray),
    }[r.status];
    const note = r.note ? color(`  (${r.note})`, COLORS.gray) : "";
    console.log(`  ${mark} ${r.status.padEnd(12)} ${r.id}${note}`);
  }

  console.log();
  console.log(
    color(
      `  ${reachable} reachable, ${unreachable} unreachable, ${inconclusive} inconclusive, ${errors} error, ${skipped} skipped`,
      COLORS.gray
    )
  );
  console.log();

  if (unreachable > 0 || errors > 0) {
    console.log(color("Witness result: ✗ FAIL", COLORS.red));
    console.log(
      color(
        "  A scenario the exhaustive model cannot reach describes an impossible outcome.",
        COLORS.gray
      )
    );
    console.log();
    process.exit(1);
  }
  console.log(color("Witness result: ✓ PASS", COLORS.green));
  console.log(
    color("  Every witnessable scenario's outcome is reachable in the model.", COLORS.gray)
  );
  console.log();
}

function displayEnsuresSummary(results: Array<{ ensuresCount: number }>): void {
  const totalEnsures = results.reduce((sum, r) => sum + r.ensuresCount, 0);
  if (totalEnsures === 0) return;

  const subsystemWord = `subsystem${results.length === 1 ? "" : "s"}`;
  console.log();
  console.log(
    color(
      `  ${totalEnsures} ensures step-properties registered across ${results.length} ${subsystemWord}.`,
      COLORS.gray
    )
  );
  console.log(
    color("  A property only fires at states where its handler is enabled — raise", COLORS.gray)
  );
  console.log(
    color(
      "  bounds.maxInFlight on a subsystem to reach multi-step-reachable handlers.",
      COLORS.gray
    )
  );
}

function displayCompositionalReport(
  results: Array<{
    name: string;
    success: boolean;
    handlerCount: number;
    ensuresCount: number;
    stateCount: number;
    elapsed: number;
  }>,
  nonInterferenceValid: boolean
): void {
  console.log(color("Subsystem verification results:\n", COLORS.blue));

  for (const r of results) {
    const status = r.success ? color("✓", COLORS.green) : color("✗", COLORS.red);
    const name = r.name.padEnd(20);
    const handlers = `${r.handlerCount} handler${r.handlerCount === 1 ? "" : "s"}`;
    const ensures = `${r.ensuresCount} ensures`;
    const states = `${r.stateCount} states`;
    const time = `${r.elapsed.toFixed(1)}s`;
    console.log(
      `  ${status} ${name} ${handlers.padEnd(14)} ${ensures.padEnd(12)} ${states.padEnd(14)} ${time}`
    );
  }

  displayEnsuresSummary(results);

  console.log();

  const nonIntLabel = nonInterferenceValid
    ? color("✓ verified (no cross-subsystem state writes)", COLORS.green)
    : color("⚠ violations detected", COLORS.yellow);
  console.log(`  Non-interference: ${nonIntLabel}`);
  console.log();

  const allPassed = results.every((r) => r.success);
  if (allPassed && nonInterferenceValid) {
    console.log(color("Compositional result: ✓ PASS", COLORS.green));
    console.log(
      color("  All subsystems verified independently. By non-interference,", COLORS.gray)
    );
    console.log(color("  the full system satisfies all per-subsystem invariants.", COLORS.gray));
  } else if (allPassed && !nonInterferenceValid) {
    console.log(color("Compositional result: ⚠ PASS (with warnings)", COLORS.yellow));
    console.log(
      color("  All subsystems passed, but non-interference violations exist.", COLORS.gray)
    );
    console.log(color("  Compositional soundness is not guaranteed.", COLORS.gray));
  } else {
    console.log(color("Compositional result: ✗ FAIL", COLORS.red));
    const failed = results.filter((r) => !r.success);
    for (const f of failed) {
      console.log(color(`  Failed: ${f.name}`, COLORS.red));
    }
    process.exit(1);
  }

  console.log();
}

async function loadVerificationConfig(configPath: string): Promise<unknown> {
  const resolvedPath = path.resolve(configPath);
  const configModule = await import(`file://${resolvedPath}?t=${Date.now()}`);

  // Support both named export (verificationConfig) and default export
  // Named export was added in v0.7.0 for better IDE support
  return configModule.verificationConfig || configModule.default;
}

async function runCodebaseAnalysis(): Promise<{ fields: unknown[]; messageTypes: unknown[] }> {
  console.log(color("📊 Analyzing codebase...", COLORS.blue));
  const tsConfigPath = findTsConfig();
  if (!tsConfigPath) {
    throw new Error("Could not find tsconfig.json");
  }

  const analysis = await analyzeCodebase({
    tsConfigPath,
    stateFilePath: findStateFile(),
  });

  console.log(color("✓ Analysis complete", COLORS.green));
  console.log();

  return analysis;
}

async function generateAndWriteTLASpecs(
  config: unknown,
  analysis: unknown
): Promise<{ specPath: string; specDir: string }> {
  const { generateTLA } = await import("./codegen/tla");

  console.log(color("📝 Generating TLA+ specification...", COLORS.blue));
  const { spec, cfg } = await generateTLA(config, analysis);

  const specDir = path.join(process.cwd(), "specs", "tla", "generated");
  if (!fs.existsSync(specDir)) {
    fs.mkdirSync(specDir, { recursive: true });
  }

  const specPath = path.join(specDir, "UserApp.tla");
  const cfgPath = path.join(specDir, "UserApp.cfg");

  fs.writeFileSync(specPath, spec);
  fs.writeFileSync(cfgPath, cfg);

  return { specPath, specDir };
}

function findAndCopyBaseSpec(specDir: string): void {
  const possiblePaths = [
    path.join(process.cwd(), "specs", "tla", "MessageRouter.tla"),
    path.join(__dirname, "..", "specs", "tla", "MessageRouter.tla"),
    path.join(__dirname, "..", "..", "specs", "tla", "MessageRouter.tla"),
    path.join(
      process.cwd(),
      "external",
      "polly",
      "packages",
      "verify",
      "specs",
      "tla",
      "MessageRouter.tla"
    ),
    path.join(
      process.cwd(),
      "node_modules",
      "@fairfox",
      "polly-verify",
      "specs",
      "tla",
      "MessageRouter.tla"
    ),
  ];

  let baseSpecPath: string | null = null;
  for (const candidatePath of possiblePaths) {
    if (fs.existsSync(candidatePath)) {
      baseSpecPath = candidatePath;
      break;
    }
  }

  if (baseSpecPath) {
    const destSpecPath = path.join(specDir, "MessageRouter.tla");
    fs.copyFileSync(baseSpecPath, destSpecPath);
    console.log(color("✓ Copied MessageRouter.tla", COLORS.green));
  } else {
    console.log(
      color("⚠️  Warning: MessageRouter.tla not found, verification may fail", COLORS.yellow)
    );
    console.log(color("   Searched in:", COLORS.gray));
    for (const searchPath of possiblePaths) {
      console.log(color(`   - ${searchPath}`, COLORS.gray));
    }
  }
}

/**
 * polly#114: locate the directory holding the committed MeshSeed.tla /
 * MeshSeed.cfg pair. Mirrors findAndCopyBaseSpec's search order.
 */
function findMeshSeedSpecDir(): string | null {
  const candidates = [
    path.join(process.cwd(), "specs", "tla"),
    path.join(__dirname, "..", "specs", "tla"),
    path.join(__dirname, "..", "..", "specs", "tla"),
    path.join(process.cwd(), "node_modules", "@fairfox", "polly-verify", "specs", "tla"),
  ];
  for (const dir of candidates) {
    if (fs.existsSync(path.join(dir, "MeshSeed.tla"))) return dir;
  }
  return null;
}

/**
 * polly#114: model-check the concurrent first-time $meshState seed.
 *
 * When the project declares mesh documents the seed path is in scope —
 * and the polly#113 race (two devices materialising the same document
 * concurrently, forking it permanently) lived entirely outside the
 * verify pipeline. This runs MeshSeed.tla alongside the project spec.
 *
 * `POLLY_113_DISABLE_FIX=1` — the same toggle seedDocumentBytes honours
 * to restore the pre-fix non-deterministic seed — flips the spec's
 * SeedDeterministic constant to FALSE. Under it TLC reports a
 * SeedConvergence violation and verification fails, so a regression in
 * the seed path cannot land green.
 *
 * Returns undefined (guard skipped) when no mesh documents are declared.
 */
async function runMeshSeedGuard(
  docker: Awaited<ReturnType<typeof setupDocker>>,
  specDir: string,
  config: unknown
): Promise<Parameters<typeof displayVerificationResults>[0] | undefined> {
  if (getMeshDocIds(config).length === 0) return undefined;

  const sourceDir = findMeshSeedSpecDir();
  if (!sourceDir) {
    console.log(color("⚠️  MeshSeed.tla not found — skipping seed-race guard", COLORS.yellow));
    return undefined;
  }

  const fixDisabled = isSeedFixDisabled();
  fs.copyFileSync(path.join(sourceDir, "MeshSeed.tla"), path.join(specDir, "MeshSeed.tla"));
  // One source of truth for Peers / invariants / properties: the
  // committed cfg. Only the SeedDeterministic constant is rewritten.
  const baseCfg = fs.readFileSync(path.join(sourceDir, "MeshSeed.cfg"), "utf8");
  fs.writeFileSync(
    path.join(specDir, "MeshSeed.cfg"),
    meshSeedCfg(baseCfg, { disableFix: fixDisabled })
  );

  console.log(
    color(
      `⚙️  Running mesh seed-race guard (MeshSeed.tla, SeedDeterministic = ${
        fixDisabled ? "FALSE" : "TRUE"
      })...`,
      COLORS.blue
    )
  );
  return docker.runTLC(path.join(specDir, "MeshSeed.tla"), { workers: 1 });
}

async function setupDocker(): Promise<{
  runTLC: (
    specPath: string,
    options: { workers: number; timeout: number }
  ) => Promise<{
    success: boolean;
    stats?: { statesGenerated: number; distinctStates: number };
    violation?: { name: string; trace: string[] };
    error?: string;
    output: string;
  }>;
}> {
  const { DockerRunner } = await import("./runner/docker");

  console.log(color("🐳 Checking Docker...", COLORS.blue));
  const docker = new DockerRunner();

  try {
    if (!(await docker.isDockerAvailable())) {
      console.log();
      console.log(color("❌ Docker is not available", COLORS.red));
      console.log();
      console.log("Please ensure Docker is installed and running:");
      console.log(
        color(
          "  • Install Docker Desktop: https://www.docker.com/products/docker-desktop",
          COLORS.gray
        )
      );
      console.log(color("  • Make sure Docker Desktop is running", COLORS.gray));
      console.log();
      throw new Error("Docker is not available");
    }
  } catch (error) {
    console.log();
    if (error instanceof Error && error.message.includes("timed out")) {
      console.log(color("❌ Docker is unresponsive", COLORS.red));
      console.log();
      console.log("Docker appears to be installed but is not responding.");
      console.log("Try restarting Docker:");
      console.log(color("  • Quit Docker Desktop completely", COLORS.gray));
      console.log(color("  • Restart Docker Desktop", COLORS.gray));
      console.log(
        color("  • Wait for Docker to fully start (check the menu bar icon)", COLORS.gray)
      );
      console.log();
    } else if (error instanceof Error && error.message !== "Docker is not available") {
      console.log(color(`❌ Error checking Docker: ${error.message}`, COLORS.red));
      console.log();
    }
    throw error;
  }

  try {
    if (!(await docker.hasImage())) {
      console.log(color("   Pulling TLA+ image (this may take a moment)...", COLORS.gray));
      await docker.pullImage((line) => {
        console.log(color(`   ${line}`, COLORS.gray));
      });
    }
  } catch (error) {
    console.log();
    if (error instanceof Error && error.message.includes("timed out")) {
      console.log(color("❌ Docker is unresponsive while checking for TLA+ image", COLORS.red));
      console.log();
      console.log("Docker is not responding. Try restarting Docker Desktop.");
      console.log();
    }
    throw error;
  }

  console.log(color("✓ Docker ready", COLORS.green));
  console.log();

  return docker;
}

function displayVerificationResults(
  result: {
    success: boolean;
    stats?: { statesGenerated: number; distinctStates: number };
    violation?: { name: string; trace: string[] };
    error?: string;
    output: string;
  },
  specDir: string
): void {
  if (result.success) {
    console.log(color("✅ Verification passed!\n", COLORS.green));
    console.log(color("Statistics:", COLORS.blue));
    console.log(color(`   States explored: ${result.stats?.statesGenerated || 0}`, COLORS.gray));
    console.log(color(`   Distinct states: ${result.stats?.distinctStates || 0}`, COLORS.gray));
    console.log();
    return;
  }

  console.log(color("❌ Verification failed!\n", COLORS.red));

  if (result.violation) {
    console.log(color(`Invariant violated: ${result.violation.name}\n`, COLORS.red));
    console.log(color("Trace to violation:", COLORS.yellow));
    for (const line of result.violation.trace.slice(0, 20)) {
      console.log(color(`  ${line}`, COLORS.gray));
    }
    if (result.violation.trace.length > 20) {
      console.log(color(`  ... (${result.violation.trace.length - 20} more lines)`, COLORS.gray));
    }
  } else if (result.error) {
    console.log(color(`Error: ${result.error}`, COLORS.red));
  }

  console.log();
  console.log(color("Full output saved to:", COLORS.gray));
  console.log(color(`  ${path.join(specDir, "tlc-output.log")}`, COLORS.gray));
  fs.writeFileSync(path.join(specDir, "tlc-output.log"), result.output);

  process.exit(1);
}

function showHelp() {
  console.log(`
${color("polly verify", COLORS.blue)} - Formal verification for web extensions

Tests sample a few executions; a model checker explores every reachable state.
This compiles your handlers and state into TLA+ and runs TLC to prove safety
invariants hold under all interleavings — the ordering and concurrency bugs
tests rarely reach.

${color("Commands:", COLORS.blue)}

  ${color("polly verify", COLORS.green)}
    Run verification (validates config, generates specs, runs TLC)

  ${color("polly verify --strict", COLORS.green)}
    Fail closed (non-zero exit) on model-coverage gaps: a declared state
    field no handler writes, or an unverified $meshState/$peerState predicate.
    Also via ${color("POLLY_VERIFY_STRICT=1", COLORS.yellow)}.

  ${color("polly verify --witness", COLORS.green)}
    After the invariant pass, check each BDD scenario's Then-outcome for
    reachability: one TLC run per witnessable scenario over its subsystem spec.
    A scenario the exhaustive model proves unreachable is one that lies, and
    fails the run. Needs a ${color("subsystems", COLORS.blue)} block and ${color("features/", COLORS.blue)} (see polly bdd).

  ${color("polly verify --setup", COLORS.green)}
    Analyze codebase and generate configuration file

  ${color("polly verify --validate", COLORS.green)}
    Validate existing configuration without running verification

  ${color("polly verify --estimate", COLORS.green)}
    Estimate state space without running TLC

  ${color("polly verify --help", COLORS.green)}
    Show this help message

${color("Getting Started:", COLORS.blue)}

  1. Run ${color("polly verify --setup", COLORS.green)} to generate configuration
  2. Review ${color("specs/verification.config.ts", COLORS.blue)} and fill in marked fields
  3. Run ${color("polly verify --validate", COLORS.green)} to check your configuration
  4. Run ${color("polly verify", COLORS.green)} to start verification

${color("Configuration Help:", COLORS.blue)}

  The generated config file uses special markers:

    ${color("/* CONFIGURE */", COLORS.yellow)}  - Replace with your value
    ${color("/* REVIEW */", COLORS.yellow)}     - Check auto-generated value
    ${color("null", COLORS.yellow)}             - Must be replaced with concrete value

${color("Learn More:", COLORS.blue)}

  Documentation: https://github.com/fairfox/web-ext
  TLA+ Resources: https://learntla.com
`);
}

function findTsConfig(): string | null {
  const locations = [
    path.join(process.cwd(), "tsconfig.json"),
    path.join(process.cwd(), "packages", "web-ext", "tsconfig.json"),
  ];

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc;
    }
  }

  return null;
}

function findStateFile(): string | undefined {
  const locations = [
    path.join(process.cwd(), "types", "state.ts"),
    path.join(process.cwd(), "src", "types", "state.ts"),
    path.join(process.cwd(), "packages", "web-ext", "src", "shared", "state", "app-state.ts"),
  ];

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc;
    }
  }

  return undefined;
}

main().catch((error) => {
  if (error instanceof Error && error.stack) {
    // Stack trace already printed by underlying functions
  }
  process.exit(1);
});
