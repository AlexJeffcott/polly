#!/usr/bin/env bun
// CLI for verification system

import * as fs from "node:fs"
import * as path from "node:path"
import { analyzeCodebase } from "./extract/types"
import { generateConfig } from "./codegen/config"
import { validateConfig } from "./config/parser"

const COLORS = {
  reset: "\x1b[0m",
  red: "\x1b[31m",
  green: "\x1b[32m",
  yellow: "\x1b[33m",
  blue: "\x1b[34m",
  gray: "\x1b[90m",
}

function color(text: string, colorCode: string): string {
  return `${colorCode}${text}${COLORS.reset}`
}

async function main() {
  const args = process.argv.slice(2)
  const command = args[0]

  switch (command) {
    case "--setup":
    case "setup":
      await setupCommand()
      break

    case "--validate":
    case "validate":
      await validateCommand()
      break

    case "--help":
    case "help":
      showHelp()
      break

    default:
      await verifyCommand()
  }
}

async function setupCommand() {
  console.log(color("\n🔍 Analyzing codebase...\n", COLORS.blue))

  try {
    // Find tsconfig
    const tsConfigPath = findTsConfig()
    if (!tsConfigPath) {
      console.error(color("❌ Could not find tsconfig.json", COLORS.red))
      console.error("   Run this command from your project root")
      process.exit(1)
    }

    console.log(color(`   Using: ${tsConfigPath}`, COLORS.gray))

    // Analyze codebase
    const analysis = await analyzeCodebase({
      tsConfigPath,
      stateFilePath: findStateFile()
    })

    if (!analysis.stateType) {
      console.log(color("\n⚠️  Could not find state type definition", COLORS.yellow))
      console.log("   Expected to find a type named 'AppState' or 'State'")
      console.log("   in a file matching **/state*.ts")
      console.log()
      console.log("   You can still generate a config template:")
      console.log("   It will be empty and you'll need to fill it in manually.")
      console.log()
    } else {
      console.log(color(`✓ Found state type with ${analysis.fields.length} field(s)`, COLORS.green))
    }

    console.log(color(`✓ Found ${analysis.messageTypes.length} message type(s)`, COLORS.green))

    // Show analysis summary
    if (analysis.fields.length > 0) {
      console.log(color("\n📊 Configuration Summary:\n", COLORS.blue))

      const table = [
        ["Field", "Type", "Status"],
        ["─".repeat(30), "─".repeat(20), "─".repeat(20)],
      ]

      for (const field of analysis.fields) {
        const status = field.confidence === "high"
          ? color("✓ Auto-configured", COLORS.green)
          : field.confidence === "medium"
          ? color("⚠ Review needed", COLORS.yellow)
          : color("⚠ Manual config", COLORS.red)

        table.push([field.path, field.type.kind, status])
      }

      for (const row of table) {
        console.log(`   ${row[0]?.padEnd(32) ?? ''} ${row[1]?.padEnd(22) ?? ''} ${row[2] ?? ''}`)
      }
    }

    // Generate config
    const configContent = generateConfig(analysis)
    const configPath = path.join(process.cwd(), "specs", "verification.config.ts")

    // Ensure directory exists
    const configDir = path.dirname(configPath)
    if (!fs.existsSync(configDir)) {
      fs.mkdirSync(configDir, { recursive: true })
    }

    // Write config
    fs.writeFileSync(configPath, configContent, "utf-8")

    console.log(color("\n✅ Configuration generated!\n", COLORS.green))
    console.log(`   File: ${color(configPath, COLORS.blue)}`)
    console.log()
    console.log(color("📝 Next steps:", COLORS.blue))
    console.log()
    console.log("   1. Review the generated configuration file")
    console.log("   2. Fill in values marked with /* CONFIGURE */")
    console.log("   3. Run 'bun verify' to check your configuration")
    console.log()
    console.log(color("💡 Tip:", COLORS.gray))
    console.log(color("   Look for comments explaining what each field needs.", COLORS.gray))
    console.log()

  } catch (error) {
    console.error(color("\n❌ Setup failed:", COLORS.red))
    console.error(`   ${error instanceof Error ? error.message : String(error)}`)
    process.exit(1)
  }
}

async function validateCommand() {
  const configPath = path.join(process.cwd(), "specs", "verification.config.ts")

  console.log(color("\n🔍 Validating configuration...\n", COLORS.blue))

  const result = validateConfig(configPath)

  if (result.valid) {
    console.log(color("✅ Configuration is complete and valid!\n", COLORS.green))
    console.log("   You can now run 'bun verify' to start verification.")
    console.log()
    return
  }

  // Show errors
  const errors = result.issues.filter(i => i.severity === "error")
  const warnings = result.issues.filter(i => i.severity === "warning")

  if (errors.length > 0) {
    console.log(color(`❌ Found ${errors.length} error(s):\n`, COLORS.red))

    for (const error of errors) {
      console.log(color(`   • ${error.message}`, COLORS.red))
      if (error.field) {
        console.log(color(`     Field: ${error.field}`, COLORS.gray))
      }
      if (error.location) {
        console.log(color(`     Location: line ${error.location.line}`, COLORS.gray))
      }
      console.log(color(`     → ${error.suggestion}`, COLORS.yellow))
      console.log()
    }
  }

  if (warnings.length > 0) {
    console.log(color(`⚠️  Found ${warnings.length} warning(s):\n`, COLORS.yellow))

    for (const warning of warnings) {
      console.log(color(`   • ${warning.message}`, COLORS.yellow))
      if (warning.field) {
        console.log(color(`     Field: ${warning.field}`, COLORS.gray))
      }
      console.log(color(`     → ${warning.suggestion}`, COLORS.gray))
      console.log()
    }
  }

  console.log(color("Configuration incomplete. Please fix the errors above.\n", COLORS.red))
  process.exit(1)
}

async function verifyCommand() {
  const configPath = path.join(process.cwd(), "specs", "verification.config.ts")

  console.log(color("\n🔍 Running verification...\n", COLORS.blue))

  // First validate config
  const validation = validateConfig(configPath)

  if (!validation.valid) {
    const errors = validation.issues.filter(i => i.severity === "error")
    console.log(color(`❌ Configuration incomplete (${errors.length} error(s))\n`, COLORS.red))

    for (const error of errors.slice(0, 3)) {
      console.log(color(`   • ${error.message}`, COLORS.red))
      if (error.field) {
        console.log(color(`     Field: ${error.field}`, COLORS.gray))
      }
      console.log()
    }

    if (errors.length > 3) {
      console.log(color(`   ... and ${errors.length - 3} more error(s)`, COLORS.gray))
      console.log()
    }

    console.log("   Run 'bun verify --validate' to see all issues")
    console.log("   Run 'bun verify --setup' to regenerate configuration")
    console.log()
    process.exit(1)
  }

  console.log(color("✓ Configuration valid", COLORS.green))
  console.log()

  // Run full verification
  try {
    await runFullVerification(configPath)
  } catch (error) {
    console.error(color("\n❌ Verification failed:", COLORS.red))
    console.error(`   ${error instanceof Error ? error.message : String(error)}`)
    process.exit(1)
  }
}

async function runFullVerification(configPath: string) {
  const { generateTLA } = await import("./codegen/tla")
  const { DockerRunner } = await import("./runner/docker")

  // Load config (using dynamic import with cache busting)
  const resolvedPath = path.resolve(configPath)
  const configModule = await import(`file://${resolvedPath}?t=${Date.now()}`)
  const config = configModule.default

  // Analyze codebase
  console.log(color("📊 Analyzing codebase...", COLORS.blue))
  const tsConfigPath = findTsConfig()
  if (!tsConfigPath) {
    throw new Error("Could not find tsconfig.json")
  }

  const analysis = await analyzeCodebase({
    tsConfigPath,
    stateFilePath: findStateFile()
  })

  console.log(color("✓ Analysis complete", COLORS.green))
  console.log()

  // Generate TLA+ specs
  console.log(color("📝 Generating TLA+ specification...", COLORS.blue))
  const { spec, cfg } = await generateTLA(config, analysis)

  // Write specs to temp directory
  const specDir = path.join(process.cwd(), "specs", "tla", "generated")
  if (!fs.existsSync(specDir)) {
    fs.mkdirSync(specDir, { recursive: true })
  }

  const specPath = path.join(specDir, "UserApp.tla")
  const cfgPath = path.join(specDir, "UserApp.cfg")

  fs.writeFileSync(specPath, spec)
  fs.writeFileSync(cfgPath, cfg)

  // Copy base MessageRouter spec to generated directory so TLC can find it
  // Try multiple locations to find MessageRouter.tla:
  // 1. User's specs/tla/MessageRouter.tla (if they've customized it)
  // 2. Package's bundled specs/tla/MessageRouter.tla (when installed via npm)
  // 3. External polly directory (when using git submodule or manual clone)
  const possiblePaths = [
    // User's custom version
    path.join(process.cwd(), "specs", "tla", "MessageRouter.tla"),

    // Package's bundled version (when installed as npm package)
    // CLI runs from dist/cli.js, so specs/ is at ../specs/
    path.join(__dirname, "..", "specs", "tla", "MessageRouter.tla"),

    // When running from source in development
    path.join(__dirname, "..", "..", "specs", "tla", "MessageRouter.tla"),

    // External polly directory (common in monorepos or git submodules)
    path.join(process.cwd(), "external", "polly", "packages", "verify", "specs", "tla", "MessageRouter.tla"),

    // Node modules (scoped package)
    path.join(process.cwd(), "node_modules", "@fairfox", "polly-verify", "specs", "tla", "MessageRouter.tla"),
  ]

  let baseSpecPath: string | null = null
  for (const candidatePath of possiblePaths) {
    if (fs.existsSync(candidatePath)) {
      baseSpecPath = candidatePath
      break
    }
  }

  if (baseSpecPath) {
    const destSpecPath = path.join(specDir, "MessageRouter.tla")
    fs.copyFileSync(baseSpecPath, destSpecPath)
    console.log(color("✓ Copied MessageRouter.tla", COLORS.green))
  } else {
    console.log(color("⚠️  Warning: MessageRouter.tla not found, verification may fail", COLORS.yellow))
    console.log(color(`   Searched in:`, COLORS.gray))
    for (const searchPath of possiblePaths) {
      console.log(color(`   - ${searchPath}`, COLORS.gray))
    }
  }

  console.log(color("✓ Specification generated", COLORS.green))
  console.log(color(`   ${specPath}`, COLORS.gray))
  console.log()

  // Check Docker
  console.log(color("🐳 Checking Docker...", COLORS.blue))
  const docker = new DockerRunner()

  if (!(await docker.isDockerAvailable())) {
    throw new Error("Docker is not available. Please install Docker and try again.")
  }

  if (!(await docker.hasImage())) {
    console.log(color("   Pulling TLA+ image (this may take a moment)...", COLORS.gray))
    await docker.pullImage((line) => {
      console.log(color(`   ${line}`, COLORS.gray))
    })
  }

  console.log(color("✓ Docker ready", COLORS.green))
  console.log()

  // Run TLC
  console.log(color("⚙️  Running TLC model checker...", COLORS.blue))
  console.log(color("   This may take a minute...", COLORS.gray))
  console.log()

  const result = await docker.runTLC(specPath, {
    workers: 2,
    timeout: 120000  // 2 minutes
  })

  // Display results
  if (result.success) {
    console.log(color("✅ Verification passed!\n", COLORS.green))
    console.log(color("Statistics:", COLORS.blue))
    console.log(color(`   States explored: ${result.stats?.statesGenerated || 0}`, COLORS.gray))
    console.log(color(`   Distinct states: ${result.stats?.distinctStates || 0}`, COLORS.gray))
    console.log()
  } else {
    console.log(color("❌ Verification failed!\n", COLORS.red))

    if (result.violation) {
      console.log(color(`Invariant violated: ${result.violation.name}\n`, COLORS.red))
      console.log(color("Trace to violation:", COLORS.yellow))
      for (const line of result.violation.trace.slice(0, 20)) {
        console.log(color(`  ${line}`, COLORS.gray))
      }
      if (result.violation.trace.length > 20) {
        console.log(color(`  ... (${result.violation.trace.length - 20} more lines)`, COLORS.gray))
      }
    } else if (result.error) {
      console.log(color(`Error: ${result.error}`, COLORS.red))
    }

    console.log()
    console.log(color("Full output saved to:", COLORS.gray))
    console.log(color(`  ${path.join(specDir, "tlc-output.log")}`, COLORS.gray))
    fs.writeFileSync(path.join(specDir, "tlc-output.log"), result.output)

    process.exit(1)
  }
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
`)
}

function findTsConfig(): string | null {
  const locations = [
    path.join(process.cwd(), "tsconfig.json"),
    path.join(process.cwd(), "packages", "web-ext", "tsconfig.json"),
  ]

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc
    }
  }

  return null
}

function findStateFile(): string | undefined {
  const locations = [
    path.join(process.cwd(), "types", "state.ts"),
    path.join(process.cwd(), "src", "types", "state.ts"),
    path.join(process.cwd(), "packages", "web-ext", "src", "shared", "state", "app-state.ts"),
  ]

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc
    }
  }

  return undefined
}

main().catch((error) => {
  console.error(color("\n❌ Fatal error:", COLORS.red))
  console.error(`   ${error instanceof Error ? error.message : String(error)}`)
  if (error instanceof Error && error.stack) {
    console.error(color("\nStack trace:", COLORS.gray))
    console.error(color(error.stack, COLORS.gray))
  }
  process.exit(1)
})
