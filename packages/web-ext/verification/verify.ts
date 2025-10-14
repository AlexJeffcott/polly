import { mkdirSync, writeFileSync } from "node:fs";
import * as path from "node:path";
// Verification script for web-ext package
import { type CodebaseAnalysis, HandlerExtractor, TLAGenerator } from "@fairfox/web-ext-verify";

// Paths relative to this script
const verificationDir = __dirname;
const outputDir = path.join(verificationDir, "output");
const tsConfigPath = path.join(verificationDir, "tsconfig.json");
const packageRoot = path.join(verificationDir, "..");

console.log("🔍 Verifying web-ext package...\n");
console.log(`  Source: ${verificationDir}`);
console.log(`  Output: ${outputDir}\n`);

// Extract handlers
console.log("📋 Step 1: Extracting handlers...");
const extractor = new HandlerExtractor(tsConfigPath);
const analysis = extractor.extractHandlers();

console.log(`  ✓ Found ${analysis.handlers.length} handler(s)`);
console.log(`  ✓ Found ${analysis.messageTypes.size} message type(s)\n`);

// Load verification config
console.log("📋 Step 2: Loading verification config...");
const { verificationConfig } = await import(path.join(verificationDir, "verify.config.ts"));
console.log("  ✓ Config loaded\n");

// Create codebase analysis
const codebaseAnalysis: CodebaseAnalysis = {
  stateType: null,
  messageTypes: Array.from(analysis.messageTypes),
  fields: [],
  handlers: analysis.handlers,
};

// Generate TLA+ specification
console.log("📋 Step 3: Generating TLA+ specification...");
const generator = new TLAGenerator();
const { spec, cfg } = generator.generate(verificationConfig, codebaseAnalysis);

console.log("  ✓ Specification generated\n");

// Write output files
console.log("📋 Step 4: Writing output files...");
mkdirSync(outputDir, { recursive: true });

const specPath = path.join(outputDir, "UserApp.tla");
const cfgPath = path.join(outputDir, "UserApp.cfg");

writeFileSync(specPath, spec);
writeFileSync(cfgPath, cfg);

console.log(`  ✓ ${specPath}`);
console.log(`  ✓ ${cfgPath}\n`);

// Display summary
console.log("=".repeat(80));
console.log("📊 Verification Summary");
console.log("=".repeat(80));
console.log();
console.log(`Handlers extracted:    ${analysis.handlers.length}`);
console.log(`Message types:         ${analysis.messageTypes.size}`);
console.log(
  `Total preconditions:   ${analysis.handlers.reduce((sum, h) => sum + h.preconditions.length, 0)}`
);
console.log(
  `Total postconditions:  ${analysis.handlers.reduce((sum, h) => sum + h.postconditions.length, 0)}`
);
console.log(
  `Total state changes:   ${analysis.handlers.reduce((sum, h) => sum + h.assignments.length, 0)}`
);
console.log();

// Display handler details
for (const handler of analysis.handlers) {
  console.log(`📝 ${handler.messageType}`);
  console.log(
    `   Location: ${path.relative(packageRoot, handler.location.file)}:${handler.location.line}`
  );
  console.log(`   Preconditions: ${handler.preconditions.length}`);
  console.log(`   Postconditions: ${handler.postconditions.length}`);
  console.log(`   State changes: ${handler.assignments.length}`);
  console.log();
}

console.log("=".repeat(80));
console.log();
console.log("✅ Verification complete!");
console.log();
console.log("Next steps:");
console.log("  1. Review the generated TLA+ specification");
console.log("  2. cd verification/output && tlc UserApp.tla -config UserApp.cfg");
console.log("  3. Fix any violations found");
console.log();
