// Test TLA+ generation

import { analyzeCodebase } from "./src/extract/types"
import { generateTLA } from "./src/codegen/tla"
import * as path from "node:path"
import * as fs from "node:fs"

async function test() {
  console.log("🧪 Testing TLA+ generation...")
  console.log()

  // Load example config
  const configPath = path.join(__dirname, "examples", "verification.config.ts")
  const configModule = await import(configPath)
  const config = configModule.default

  // Analyze example state
  const stateFilePath = path.join(__dirname, "examples", "state.ts")
  const tempTsConfig = path.join(__dirname, "temp.tsconfig.json")

  fs.writeFileSync(tempTsConfig, JSON.stringify({
    compilerOptions: {
      target: "ES2020",
      module: "ESNext",
      moduleResolution: "bundler",
      strict: true,
      esModuleInterop: true,
      skipLibCheck: true,
      lib: ["ES2020", "DOM"]
    },
    include: ["examples/**/*"]
  }, null, 2))

  try {
    const analysis = await analyzeCodebase({
      tsConfigPath: tempTsConfig,
      stateFilePath
    })

    console.log("✅ Analysis complete")
    console.log(`   Fields: ${analysis.fields.length}`)
    console.log()

    // Generate TLA+ spec
    console.log("📝 Generating TLA+ specification...")
    const { spec, cfg } = generateTLA(config, analysis)

    console.log("✅ Generation complete!")
    console.log()

    // Write to output
    const outputDir = path.join(__dirname, "examples", "generated")
    if (!fs.existsSync(outputDir)) {
      fs.mkdirSync(outputDir, { recursive: true })
    }

    const specPath = path.join(outputDir, "UserApp.tla")
    const cfgPath = path.join(outputDir, "UserApp.cfg")

    fs.writeFileSync(specPath, spec)
    fs.writeFileSync(cfgPath, cfg)

    console.log("📄 Generated files:")
    console.log(`   ${specPath}`)
    console.log(`   ${cfgPath}`)
    console.log()

    console.log("═".repeat(80))
    console.log("UserApp.tla:")
    console.log("═".repeat(80))
    console.log(spec)
    console.log()

    console.log("═".repeat(80))
    console.log("UserApp.cfg:")
    console.log("═".repeat(80))
    console.log(cfg)
    console.log()

  } finally {
    if (fs.existsSync(tempTsConfig)) {
      fs.unlinkSync(tempTsConfig)
    }
  }
}

test().catch(console.error)
