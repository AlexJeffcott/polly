// Public API for @fairfox/polly/teach
//
// Provides programmatic access to teaching material generation

import type {
  ArchitectureAnalysis,
  ContextInfo,
  MessageFlow,
} from "../../analysis/src/types/architecture.ts";

export interface TeachingMaterial {
  analysis: ArchitectureAnalysis;
  visualization: string;
  formattedOutput: string;
}

export interface TeachOptions {
  projectRoot: string;
  tsConfigPath?: string;
}

/**
 * Generate teaching material for a Polly project
 *
 * @param options Configuration options
 * @returns Teaching material including analysis, visualization, and formatted output
 *
 * @example
 * ```typescript
 * import { generateTeachingMaterial } from '@fairfox/polly/teach'
 *
 * const material = await generateTeachingMaterial({
 *   projectRoot: process.cwd()
 * })
 *
 * console.log(material.formattedOutput)
 * ```
 */
export async function generateTeachingMaterial(options: TeachOptions): Promise<TeachingMaterial> {
  const { analyzeArchitecture } = await import("../../analysis/src/index.ts");
  const { generateStructurizrDSL } = await import("../../visualize/src/codegen/structurizr.ts");

  const tsConfigPath = options.tsConfigPath || `${options.projectRoot}/tsconfig.json`;

  // Run architecture analysis
  const analysis = await analyzeArchitecture({
    projectRoot: options.projectRoot,
    tsConfigPath,
  });

  // Generate visualization
  const visualization = await generateStructurizrDSL(analysis);

  // Format teaching material
  const formattedOutput = formatTeachingMaterial(analysis, visualization);

  return {
    analysis,
    visualization,
    formattedOutput,
  };
}

/**
 * Format analysis results as teaching material
 */
function formatTeachingMaterial(analysis: ArchitectureAnalysis, dsl: string): string {
  const contexts = Object.entries(analysis.contexts) as [string, ContextInfo][];
  const allHandlers = contexts.flatMap(([_, ctx]) => ctx.handlers || []);
  const messageFlows = analysis.messageFlows || [];

  return `
# Polly Project Analysis

## Architecture

Your project contains ${contexts.length} context(s) and ${allHandlers.length} message handler(s).

### Contexts

${contexts
  .map(([name, ctx]) => {
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
  `.trim();
}
