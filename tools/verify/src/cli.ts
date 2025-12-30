#!/usr/bin/env bun
// CLI for verification system

import * as fs from "node:fs";
import * as path from "node:path";
import { generateConfig } from "./codegen/config";
import { validateConfig } from "./config/parser";
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
    // Log the error for debugging
    console.error(color("\n❌ Verification error:", COLORS.red));
    if (error instanceof Error) {
      console.error(color(error.message, COLORS.red));
      if (process.env.POLLY_DEBUG) {
        console.error(color("\nStack trace:", COLORS.gray));
        console.error(error.stack);
      }
    } else {
      console.error(String(error));
    }
    console.error();
    process.exit(1);
  }
}

/**
 * Get timeout in seconds based on config or preset
 */
function getTimeout(config: any): number {
  // Explicit timeout in config takes precedence
  if (config.verification?.timeout !== undefined) {
    return config.verification.timeout;
  }

  // Use preset-based defaults
  const preset = config.preset || "balanced";
  switch (preset) {
    case "quick":
      return 60; // 1 minute
    case "balanced":
      return 300; // 5 minutes
    case "thorough":
      return 0; // No timeout
    default:
      return 300; // Default to balanced
  }
}

/**
 * Get number of workers based on config or preset
 */
function getWorkers(config: any): number {
  // Explicit workers in config takes precedence
  if (config.verification?.workers !== undefined) {
    return config.verification.workers;
  }

  // Use preset-based defaults
  const preset = config.preset || "balanced";
  switch (preset) {
    case "quick":
      return 1;
    case "balanced":
      return 2;
    case "thorough":
      return 4;
    default:
      return 2; // Default to balanced
  }
}

async function runFullVerification(configPath: string) {
  // Load config
  const config = await loadVerificationConfig(configPath);

  // Analyze codebase
  const analysis = await runCodebaseAnalysis();

  // Generate TLA+ specs
  const { specPath, specDir } = await generateAndWriteTLASpecs(config, analysis);

  // Find and copy base spec
  findAndCopyBaseSpec(specDir);

  console.log(color("✓ Specification generated", COLORS.green));
  console.log(color(`   ${specPath}`, COLORS.gray));
  console.log();

  // Setup and run Docker
  const docker = await setupDocker();

  // Determine timeout and workers from config
  const timeoutSeconds = getTimeout(config);
  const workers = getWorkers(config);

  // Run TLC
  console.log(color("⚙️  Running TLC model checker...", COLORS.blue));
  if (timeoutSeconds === 0) {
    console.log(color("   No timeout set - will run until completion", COLORS.gray));
  } else {
    const timeoutMinutes = Math.floor(timeoutSeconds / 60);
    const timeoutLabel = timeoutMinutes > 0
      ? `${timeoutMinutes} minute${timeoutMinutes > 1 ? "s" : ""}`
      : `${timeoutSeconds} seconds`;
    console.log(color(`   Timeout: ${timeoutLabel}`, COLORS.gray));
  }
  console.log();

  const result = await docker.runTLC(specPath, {
    workers,
    timeout: timeoutSeconds > 0 ? timeoutSeconds * 1000 : undefined,
  });

  // Display results
  displayVerificationResults(result, specDir);
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

  if (!(await docker.isDockerAvailable())) {
    throw new Error("Docker is not available. Please install Docker and try again.");
  }

  if (!(await docker.hasImage())) {
    console.log(color("   Pulling TLA+ image (this may take a moment)...", COLORS.gray));
    await docker.pullImage((line) => {
      console.log(color(`   ${line}`, COLORS.gray));
    });
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
