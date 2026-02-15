#!/usr/bin/env bun
// CLI for verification system

import * as fs from "node:fs";
import * as path from "node:path";
import { type ValidationResult, validateExpressions } from "./analysis/expression-validator";
import {
  estimateStateSpace,
  feasibilityLabel,
  type StateSpaceEstimate,
} from "./analysis/state-space-estimator";
import { generateConfig } from "./codegen/config";
import { validateConfig } from "./config/parser";
import type { UnifiedVerificationConfig } from "./config/types";
import { analyzeCodebase } from "./extract/types";

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
  console.log("   3. Run 'bun verify' to check your configuration");
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
    console.log("   You can now run 'bun verify' to start verification.");
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
  const typedConfig = config as import("./config/types").UnifiedVerificationConfig;
  const typedAnalysis = analysis as import("./core/model").CodebaseAnalysis;
  const exprValidation = validateExpressions(typedAnalysis.handlers, typedConfig.state);
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
    `  Contexts:               ${estimate.contextCount} (${estimate.contextCount - 1} tab${estimate.contextCount - 1 !== 1 ? "s" : ""} + background)`
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

    console.log("   Run 'bun verify --validate' to see all issues");
    console.log("   Run 'bun verify --setup' to regenerate configuration");
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

async function runFullVerification(configPath: string) {
  // Load config
  const config = await loadVerificationConfig(configPath);

  // Analyze codebase
  const analysis = await runCodebaseAnalysis();

  // Validate expressions
  const typedConfig = config as UnifiedVerificationConfig;
  const typedAnalysis = analysis as import("./core/model").CodebaseAnalysis;
  const exprValidation = validateExpressions(typedAnalysis.handlers, typedConfig.state);
  if (exprValidation.warnings.length > 0) {
    displayExpressionWarnings(exprValidation);
  }

  // Check for subsystem-scoped verification
  if (typedConfig.subsystems && Object.keys(typedConfig.subsystems).length > 0) {
    await runSubsystemVerification(typedConfig, typedAnalysis);
    return;
  }

  // Monolithic verification (fallback)
  await runMonolithicVerification(config, analysis);
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
  const typedConfig = config as UnifiedVerificationConfig;
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

  // Display results
  displayVerificationResults(result, specDir);
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Subsystem orchestration requires sequential steps with branching
async function runSubsystemVerification(
  config: UnifiedVerificationConfig,
  analysis: import("./core/model").CodebaseAnalysis
) {
  const subsystems = config.subsystems as Record<string, { state: string[]; handlers: string[] }>;
  const subsystemNames = Object.keys(subsystems);

  console.log(
    color(`📦 Subsystem-scoped verification (${subsystemNames.length} subsystems)\n`, COLORS.blue)
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

function displayCompositionalReport(
  results: Array<{
    name: string;
    success: boolean;
    handlerCount: number;
    stateCount: number;
    elapsed: number;
  }>,
  nonInterferenceValid: boolean
): void {
  console.log(color("Subsystem verification results:\n", COLORS.blue));

  for (const r of results) {
    const status = r.success ? color("✓", COLORS.green) : color("✗", COLORS.red);
    const name = r.name.padEnd(20);
    const handlers = `${r.handlerCount} handler${r.handlerCount !== 1 ? "s" : ""}`;
    const states = `${r.stateCount} states`;
    const time = `${r.elapsed.toFixed(1)}s`;
    console.log(`  ${status} ${name} ${handlers.padEnd(14)} ${states.padEnd(14)} ${time}`);
  }

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
${color("bun verify", COLORS.blue)} - Formal verification for web extensions

${color("Commands:", COLORS.blue)}

  ${color("bun verify", COLORS.green)}
    Run verification (validates config, generates specs, runs TLC)

  ${color("bun verify --setup", COLORS.green)}
    Analyze codebase and generate configuration file

  ${color("bun verify --validate", COLORS.green)}
    Validate existing configuration without running verification

  ${color("bun verify --estimate", COLORS.green)}
    Estimate state space without running TLC

  ${color("bun verify --help", COLORS.green)}
    Show this help message

${color("Getting Started:", COLORS.blue)}

  1. Run ${color("bun verify --setup", COLORS.green)} to generate configuration
  2. Review ${color("specs/verification.config.ts", COLORS.blue)} and fill in marked fields
  3. Run ${color("bun verify --validate", COLORS.green)} to check your configuration
  4. Run ${color("bun verify", COLORS.green)} to start verification

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
