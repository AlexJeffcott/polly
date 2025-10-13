// Demo script to show config generation

import { analyzeCodebase } from "./src/extract/types"
import { generateConfig } from "./src/codegen/config"
import * as path from "node:path"
import * as fs from "node:fs"

async function demo() {
  console.log("🔍 Analyzing example state type...")
  console.log()

  // Use the example state file
  const stateFilePath = path.join(__dirname, "examples", "state.ts")

  // Create a minimal tsconfig for the example
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

    console.log("✅ Analysis complete!")
    console.log()
    console.log(`State type: ${analysis.stateType?.name}`)
    console.log(`Fields found: ${analysis.fields.length}`)
    console.log(`Message types: ${analysis.messageTypes.length}`)
    console.log()

    // Show field summary
    console.log("Field Analysis:")
    console.log("─".repeat(80))
    for (const field of analysis.fields) {
      const confidence = field.confidence === "high" ? "✓" :
                        field.confidence === "medium" ? "⚠" : "❌"
      console.log(`${confidence} ${field.path.padEnd(30)} ${field.type.kind.padEnd(15)} [${field.confidence}]`)
    }
    console.log()

    // Generate config
    console.log("📝 Generating configuration...")
    console.log()

    const config = generateConfig(analysis)

    // Write to temp file to show
    const outputPath = path.join(__dirname, "demo-output.config.ts")
    fs.writeFileSync(outputPath, config)

    console.log("✅ Configuration generated!")
    console.log()
    console.log(`Output file: ${outputPath}`)
    console.log()
    console.log("Preview:")
    console.log("═".repeat(80))
    console.log(config)
    console.log("═".repeat(80))

  } finally {
    // Cleanup
    if (fs.existsSync(tempTsConfig)) {
      fs.unlinkSync(tempTsConfig)
    }
  }
}

demo().catch(console.error)
