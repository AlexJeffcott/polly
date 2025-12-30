#!/usr/bin/env bun
// CLI for Polly teaching system - Claude-powered

import Anthropic from "@anthropic-ai/sdk";
import { analyzeArchitecture } from "../../analysis/src/index.ts";
import { generateStructurizrDSL } from "../../visualize/src/codegen/structurizr.ts";
import { buildTeachingContext } from "./context-builder.ts";
import { generateOptimizationPrompt, generateTeachingPrompt } from "./system-prompt.ts";

async function main() {
  const cwd = process.cwd();

  // Check for mode flag
  const args = process.argv.slice(2);
  const modeArg = args.find((arg) => arg.startsWith("--mode="));
  const mode = modeArg ? modeArg.split("=")[1] : "teach";

  // Check for API key
  const apiKey = process.env.ANTHROPIC_API_KEY;
  if (!apiKey) {
    // biome-ignore lint/suspicious/noConsole: CLI error output
    console.error("\n❌ Error: ANTHROPIC_API_KEY environment variable not set");
    // biome-ignore lint/suspicious/noConsole: CLI error output
    console.error("\nTo use polly teach, you need a Claude API key:");
    // biome-ignore lint/suspicious/noConsole: CLI error output
    console.error("1. Get an API key from https://console.anthropic.com/");
    // biome-ignore lint/suspicious/noConsole: CLI error output
    console.error("2. Set the environment variable:");
    // biome-ignore lint/suspicious/noConsole: CLI error output
    console.error("   export ANTHROPIC_API_KEY=your_key_here");
    // biome-ignore lint/suspicious/noConsole: CLI error output
    console.error("\nAlternatively, add it to your shell profile (.bashrc, .zshrc, etc.)\n");
    process.exit(1);
  }

  console.log(
    mode === "optimize" ? "Analyzing verification setup..." : "Analyzing Polly project..."
  );
  console.log();

  try {
    // Run architecture analysis
    const analysis = await analyzeArchitecture({
      projectRoot: cwd,
      tsConfigPath: `${cwd}/tsconfig.json`,
    });

    // Generate visualization
    const dsl = await generateStructurizrDSL(analysis);

    // Build teaching context
    const context = await buildTeachingContext(cwd, analysis);

    // Display appropriate overview based on mode
    if (mode === "optimize") {
      displayOptimizationOverview(context);
    } else {
      displayProjectOverview(context, dsl);
    }

    // Start Claude-powered interactive session
    await startClaudeSession(apiKey, context, mode);
  } catch (error) {
    console.log(`\n❌ Failed to analyze project: ${error}`);
    process.exit(1);
  }
}

function displayProjectOverview(context: ReturnType<typeof buildTeachingContext>, dsl: string) {
  const contexts = Object.entries(context.project.architecture.contexts);
  const _allHandlers = contexts.flatMap(
    ([_, ctx]: [string, { handlers?: unknown[] }]) => ctx.handlers || []
  );
  const messageFlows = context.project.architecture.messageFlows || [];

  console.log(
    `
# Polly Project Analysis

## Architecture

${context.project.summary}

### Contexts

${contexts
  .map(
    ([name, ctx]: [
      string,
      { entryPoint: string; handlers?: unknown[]; state?: { variables?: Record<string, unknown> } },
    ]) => {
      return `
**${name}**
Location: ${ctx.entryPoint}
Handlers: ${ctx.handlers?.length || 0}
State variables: ${Object.keys(ctx.state?.variables || {}).length}`;
    }
  )
  .join("\n")}

### Message Flows

${
  messageFlows.length > 0
    ? messageFlows
        .map((flow: { from: string; to: string; messageType: string }) => {
          return `- ${flow.from} → ${flow.to}: ${flow.messageType}`;
        })
        .join("\n")
    : "No message flows detected."
}

## Architecture Diagram

\`\`\`structurizr
${dsl}
\`\`\`

---

What would you like to understand about your project?

I'm powered by Claude and have full context of your Polly project's architecture,
handlers, state, message flows, and verification configuration. Ask me anything!
    `.trim()
  );
}

function displayOptimizationOverview(context: Awaited<ReturnType<typeof buildTeachingContext>>) {
  let output = "# Verification Optimization Session\n\n";
  output += "## Current Setup\n\n";
  output += `${context.project.summary}\n\n`;

  if (context.verification?.config) {
    output += "### Verification Configuration\n\n";
    output += "Config found at `specs/verification.config.ts`\n";

    if (context.verification.lastResults) {
      output += "\n### Last Verification Results\n\n";
      output += context.verification.lastResults.success ? "✓ Passed\n" : "✗ Failed\n";

      if (context.verification.lastResults.stats) {
        output += `- States explored: ${context.verification.lastResults.stats.statesGenerated}\n`;
        output += `- Distinct states: ${context.verification.lastResults.stats.distinctStates}\n`;
      }

      if (context.verification.lastResults.timestamp) {
        output += `- Run at: ${context.verification.lastResults.timestamp.toLocaleString()}\n`;
      }
    }
  } else {
    output += "### No Verification Setup\n\n";
    output += "Run `polly verify --setup` to configure verification.\n";
  }

  output += "\n---\n\n";
  output += "I'll analyze your verification setup and suggest optimizations to:\n";
  output += "- Reduce verification time while maintaining precision\n";
  output += "- Implement safe state space reductions\n";
  output += "- Configure optimal bounds and constraints\n\n";
  output += 'Ask me about specific optimizations or say "analyze" for a full assessment.\n';

  console.log(output);
}

async function startClaudeSession(
  apiKey: string,
  context: Awaited<ReturnType<typeof buildTeachingContext>>,
  mode: string = "teach"
) {
  const anthropic = new Anthropic({ apiKey });
  const systemPrompt =
    mode === "optimize" ? generateOptimizationPrompt(context) : generateTeachingPrompt(context);

  // Initialize conversation history
  const conversationHistory: Array<{
    role: "user" | "assistant";
    content: string;
  }> = [];

  const readline = await import("node:readline");
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    prompt: "\n\nPrompt: ",
  });

  rl.prompt();

  rl.on("line", async (input: string) => {
    const query = input.trim();

    if (!query || query === "exit" || query === "quit") {
      console.log("\nGoodbye!");
      rl.close();
      process.exit(0);
    }

    // Add user message to history
    conversationHistory.push({
      role: "user",
      content: query,
    });

    try {
      // Call Claude API
      const response = await anthropic.messages.create({
        model: "claude-sonnet-4-20250514",
        max_tokens: 4096,
        system: systemPrompt,
        messages: conversationHistory,
      });

      const assistantMessage = response.content[0];
      if (assistantMessage.type === "text") {
        const text = assistantMessage.text;

        // Add assistant message to history
        conversationHistory.push({
          role: "assistant",
          content: text,
        });

        // Display response
        console.log(`\n${text}`);
      }
    } catch (error) {
      if (error instanceof Anthropic.APIError) {
        // biome-ignore lint/suspicious/noConsole: CLI error output
        console.error(`\n❌ API Error: ${error.message}`);
        if (error.status === 401) {
          // biome-ignore lint/suspicious/noConsole: CLI error output
          console.error("Your API key may be invalid. Please check ANTHROPIC_API_KEY.");
        }
      } else {
        // biome-ignore lint/suspicious/noConsole: CLI error output
        console.error(`\n❌ Error: ${error}`);
      }
    }

    rl.prompt();
  });

  rl.on("close", () => {
    console.log("\nGoodbye!");
    process.exit(0);
  });
}

main();
