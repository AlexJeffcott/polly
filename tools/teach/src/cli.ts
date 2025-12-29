#!/usr/bin/env bun
// CLI for Polly teaching system

import { analyzeArchitecture } from "../../analysis/src/index.ts";
import type { ContextInfo, MessageFlow } from "../../analysis/src/types/architecture.ts";
import { generateStructurizrDSL } from "../../visualize/src/codegen/structurizr.ts";

async function main() {
  const cwd = process.cwd();

  console.log("Analyzing Polly project...");
  console.log();

  try {
    // Run architecture analysis
    const analysis = await analyzeArchitecture({
      projectRoot: cwd,
      tsConfigPath: `${cwd}/tsconfig.json`,
    });

    // Generate visualization
    const dsl = await generateStructurizrDSL(analysis);

    // Format and present teaching material
    const contexts = Object.entries(analysis.contexts);
    const allHandlers = contexts.flatMap(([_, ctx]: [string, ContextInfo]) => ctx.handlers || []);
    const messageFlows = analysis.messageFlows || [];

    console.log(
      `
# Polly Project Analysis

## Architecture

Your project contains ${contexts.length} context(s) and ${allHandlers.length} message handler(s).

### Contexts

${contexts
  .map(([name, ctx]: [string, ContextInfo]) => {
    return `
**${name}**
Location: ${ctx.entryPoint}
Handlers: ${ctx.handlers?.length || 0}
State variables: ${Object.keys(ctx.state?.variables || {}).length}`;
  })
  .join("\n")}

### Message Flows

${
  messageFlows.length > 0
    ? messageFlows
        .map((flow: MessageFlow) => {
          return `- ${flow.from} → ${flow.to}: ${flow.messageType}`;
        })
        .join("\n")
    : "No message flows detected."
}

## Translation Example

${
  allHandlers.length > 0
    ? `
Consider this handler from your codebase:

\`\`\`typescript
// ${allHandlers[0].file}:${allHandlers[0].location?.line || "?"}
${allHandlers[0].code || allHandlers[0].name || "Handler code not available"}
\`\`\`

Polly can translate this to TLA+ for formal verification.`
    : "No handlers detected in your project."
}

## Architecture Diagram

\`\`\`structurizr
${dsl}
\`\`\`

---

What would you like to understand?

Possible topics:
- Architecture analysis methodology
- Specific context or handler
- TypeScript to TLA+ translation rules
- Verification properties and their meaning
- Interpreting verification results
- TLA+ specification structure
    `.trim()
    );

    console.log("\n\nPrompt: ");
  } catch (error) {
    console.log(`\n❌ Failed to analyze project: ${error}`);
    process.exit(1);
  }
}

main();
