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

    // Start interactive REPL
    await startREPL(analysis, dsl);
  } catch (error) {
    console.log(`\n❌ Failed to analyze project: ${error}`);
    process.exit(1);
  }
}

async function startREPL(analysis: any, dsl: string) {
  const readline = await import("readline");
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    prompt: "\n\nPrompt: ",
  });

  const contexts = Object.entries(analysis.contexts);
  const allHandlers = contexts.flatMap(([_, ctx]: [string, ContextInfo]) => ctx.handlers || []);
  const messageFlows = analysis.messageFlows || [];

  rl.prompt();

  rl.on("line", (input: string) => {
    const query = input.trim().toLowerCase();

    if (!query || query === "exit" || query === "quit") {
      console.log("\nGoodbye!");
      rl.close();
      process.exit(0);
    }

    // Handle different query types
    if (query.includes("architecture") || query.includes("methodology")) {
      console.log(`
Architecture Analysis Methodology
================================

Polly analyzes your codebase by:

1. **Context Discovery**: Identifies all execution contexts (background, popup, content scripts, etc.)
   - Scans for \`createBackgroundContext()\`, \`createUIContext()\`, etc.
   - Each context has its own message handlers and state

2. **Handler Detection**: Finds message handlers in each context
   - Looks for \`onMessage()\` calls
   - Extracts handler logic and dependencies

3. **State Analysis**: Tracks reactive state variables
   - Identifies Preact signals and computed values
   - Maps state dependencies between handlers

4. **Message Flow Mapping**: Traces messages between contexts
   - Detects \`sendMessage()\` calls
   - Builds communication graph

5. **Pattern Recognition**: Classifies handlers by pattern
   - Query (read operations)
   - Command (write operations)
   - Authentication, CRUD, etc.

Your project has:
- ${contexts.length} context(s)
- ${allHandlers.length} handler(s)
- ${messageFlows.length} message flow(s)
      `.trim());
    } else if (query.includes("context") || query.includes("handler")) {
      console.log(`
Contexts and Handlers in Your Project
====================================

${contexts
  .map(([name, ctx]: [string, ContextInfo]) => {
    const handlers = ctx.handlers || [];
    return `
**${name}** Context
- Location: ${ctx.entryPoint}
- Handlers: ${handlers.length}
- State Variables: ${Object.keys(ctx.state?.variables || {}).length}

Handlers:
${handlers.map((h) => `  - ${h.name} (${h.file}:${h.location?.line || "?"})`).join("\n") || "  None"}
`;
  })
  .join("\n")}
      `.trim());
    } else if (query.includes("tla") || query.includes("translation")) {
      console.log(`
TypeScript to TLA+ Translation
=============================

Polly can translate your message handlers to TLA+ for formal verification.

Translation Rules:
- Message handlers → TLA+ actions
- State variables → TLA+ variables
- Async operations → Non-deterministic choices
- Chrome APIs → Abstract operations

Example from your project:
${
  allHandlers.length > 0
    ? `
\`\`\`typescript
// ${allHandlers[0].file}:${allHandlers[0].location?.line || "?"}
${allHandlers[0].code || allHandlers[0].name || "Handler code not available"}
\`\`\`

This would translate to a TLA+ action that:
1. Checks preconditions
2. Updates state variables
3. Sends response messages
`
    : "No handlers available for translation example"
}

Use \`polly verify\` to generate and check TLA+ specifications.
      `.trim());
    } else if (query.includes("verification") || query.includes("properties")) {
      console.log(`
Verification Properties
=====================

Polly verifies these properties of your system:

1. **Safety Properties**
   - No invalid state transitions
   - Type safety maintained
   - No race conditions

2. **Liveness Properties**
   - Messages eventually delivered
   - Handlers eventually respond
   - No deadlocks

3. **Consistency Properties**
   - State synchronized across contexts
   - No conflicting updates

To verify your project:
\`\`\`bash
polly verify --setup  # First time setup
polly verify          # Run verification
\`\`\`

The verification will check all ${allHandlers.length} handlers in your project.
      `.trim());
    } else if (query.includes("result") || query.includes("interpret")) {
      console.log(`
Interpreting Verification Results
================================

TLC (TLA+ model checker) output:

✅ **Success**: "Model checking completed. No error has been found."
   - Your system is correct for the checked scenarios
   - All properties hold

❌ **Error Found**: Shows a counterexample trace
   - Step-by-step execution leading to violation
   - Variable states at each step
   - Helps identify the bug

⚠️ **Deadlock**: System can reach a state with no enabled actions
   - Usually indicates missing handlers or blocked operations

📊 **Statistics**:
   - States explored: How many system states checked
   - Distinct states: Unique states found
   - Depth: Longest execution sequence

Use the trace to understand and fix issues.
      `.trim());
    } else if (query.includes("specification") || query.includes("structure")) {
      console.log(`
TLA+ Specification Structure
===========================

A Polly-generated TLA+ spec contains:

1. **MODULE Header**: Declares the module name

2. **EXTENDS**: Imports standard TLA+ modules (Naturals, Sequences, etc.)

3. **VARIABLES**: Declares state variables
   - One per reactive signal in your code
   - Message queues between contexts

4. **Init**: Initial state
   - Sets starting values for all variables

5. **Actions**: One per message handler
   - Preconditions (when handler can run)
   - State updates (effect of handler)

6. **Next**: Defines all possible transitions
   - Disjunction of all actions
   - Represents any single step

7. **Spec**: The complete specification
   - Init ∧ [][Next]_vars
   - Means: start in Init, then repeatedly apply Next

Your ${allHandlers.length} handlers become ${allHandlers.length} TLA+ actions.
      `.trim());
    } else if (query.includes("diagram") || query.includes("visual")) {
      console.log(`
Architecture Diagram
==================

Your architecture in Structurizr DSL format:

\`\`\`structurizr
${dsl}
\`\`\`

To visualize this:
1. Visit https://structurizr.com/dsl
2. Paste the DSL code above
3. Explore the interactive diagram

Or use the CLI:
\`\`\`bash
polly visualize --serve  # Opens browser with diagram
\`\`\`
      `.trim());
    } else if (query.includes("help") || query === "?") {
      console.log(`
Available Topics
===============

Ask about:
- "architecture" or "methodology" - How Polly analyzes your code
- "context" or "handler" - Details about your contexts and handlers
- "tla" or "translation" - How TypeScript becomes TLA+
- "verification" or "properties" - What properties are verified
- "results" or "interpret" - Understanding verification output
- "specification" or "structure" - TLA+ spec structure
- "diagram" or "visual" - Architecture visualization

Commands:
- "help" or "?" - Show this help
- "exit" or "quit" - Exit the teach mode
- Just press Enter - Exit
      `.trim());
    } else {
      console.log(`
I can help explain:
- Architecture analysis methodology
- Your specific contexts and handlers
- TypeScript to TLA+ translation rules
- Verification properties and their meaning
- Interpreting verification results
- TLA+ specification structure
- Architecture diagrams

Type "help" to see all available topics, or ask a question!
      `.trim());
    }

    rl.prompt();
  });

  rl.on("close", () => {
    console.log("\nGoodbye!");
    process.exit(0);
  });
}

main();
