import { mkdirSync, writeFileSync } from "node:fs";
import * as path from "node:path";
// Verification script for web-ext package
import { type CodebaseAnalysis, HandlerExtractor, TLAGenerator } from "@fairfox/web-ext-verify";

// Paths relative to this script
const verificationDir = __dirname;
const outputDir = path.join(verificationDir, "output");
const tsConfigPath = path.join(verificationDir, "tsconfig.json");
const _packageRoot = path.join(verificationDir, "..");
const extractor = new HandlerExtractor(tsConfigPath);
const analysis = extractor.extractHandlers();
const { verificationConfig } = await import(path.join(verificationDir, "verify.config.ts"));

// Create codebase analysis
const codebaseAnalysis: CodebaseAnalysis = {
  stateType: null,
  messageTypes: Array.from(analysis.messageTypes),
  fields: [],
  handlers: analysis.handlers,
};
const generator = new TLAGenerator();
const { spec, cfg } = generator.generate(verificationConfig, codebaseAnalysis);
mkdirSync(outputDir, { recursive: true });

const specPath = path.join(outputDir, "UserApp.tla");
const cfgPath = path.join(outputDir, "UserApp.cfg");

writeFileSync(specPath, spec);
writeFileSync(cfgPath, cfg);
