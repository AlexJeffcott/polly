// System prompt generator for Claude-powered teaching

import type { TeachingContext } from "./context-builder.ts";
import type { ContextInfo, MessageFlow } from "../../analysis/src/types/architecture.ts";

/**
 * Generate teaching system prompt with project context
 */
export function generateTeachingPrompt(context: TeachingContext): string {
  const contexts = Object.entries(context.project.architecture.contexts) as [string, ContextInfo][];
  const allHandlers = contexts.flatMap(([_, ctx]) => ctx.handlers || []);
  const messageFlows = context.project.architecture.messageFlows || [];

  return `You are an expert instructor teaching a developer about their Polly project and formal verification.

# Communication Style

- Direct and precise language
- No emojis or decorative elements
- No florid language or superlatives
- Classic style: clear and simple as truth
- Academic rigor without unnecessary ornamentation
- Act like an Oxford university professor

# Your Project Context

${generateProjectSection(context, contexts, allHandlers, messageFlows)}

${generateVerificationSection(context)}

# Your Role

1. **Understand their project**: Use the architecture analysis to explain their specific codebase
2. **Teach Polly concepts**: Explain how Polly's analysis, verification, and visualization work
3. **Explain formal verification**: Teach TLA+ and verification concepts using their actual code as examples
4. **Debug and optimize**: Help interpret verification results and suggest improvements
5. **Answer questions directly**: Address their specific questions with precise technical answers

# Key Areas You Can Help With

- **Architecture**: How contexts, handlers, and message flows work in their project
- **Translation**: How TypeScript code becomes TLA+ specifications
- **Verification**: What properties are being verified and what they mean
- **Performance**: How to optimize verification speed and state space exploration
- **Debugging**: Interpreting counterexamples and fixing violations
- **Configuration**: Understanding maxInFlight, bounds, and other verification parameters

# Important Notes

- Always reference specific code from their project when explaining concepts
- If asked about verification performance, consider the verification config and results
- Provide actionable suggestions, not just general advice
- If you don't know something specific about their project, say so clearly

Begin by understanding their question and providing a clear, precise answer based on their project context.`;
}

function generateProjectSection(
  context: TeachingContext,
  contexts: [string, ContextInfo][],
  handlers: unknown[],
  flows: MessageFlow[]
): string {
  let section = `## Architecture Overview

${context.project.summary}

### Contexts

${contexts
  .map(([name, ctx]) => {
    const handlerList = ctx.handlers || [];
    const stateVars = Object.keys(ctx.state?.variables || {});
    return `**${name}**
- Entry point: ${ctx.entryPoint}
- Handlers: ${handlerList.length}
- State variables: ${stateVars.join(", ") || "none"}`;
  })
  .join("\n\n")}

### Message Flows

${
  flows.length > 0
    ? flows
        .map((flow: MessageFlow) => {
          return `- ${flow.from} → ${flow.to}: ${flow.messageType}`;
        })
        .join("\n")
    : "No message flows detected."
}

### Handlers

Total handlers: ${handlers.length}

${
  handlers.length > 0
    ? `Example handlers from the project:
${handlers
  .slice(0, 3)
  .map((h: { name: string; file: string; location?: { line: number } }) => {
    return `- ${h.name} (${h.file}:${h.location?.line || "?"})`;
  })
  .join("\n")}`
    : ""
}`;

  return section;
}

function generateVerificationSection(context: TeachingContext): string {
  if (!context.verification) {
    return `## Verification Status

No verification has been configured yet. To set up verification:
1. Run \`polly verify --setup\`
2. Review and configure \`specs/verification.config.ts\`
3. Run \`polly verify\` to start verification`;
  }

  let section = "## Verification\n\n";

  if (context.verification.config) {
    section += "### Configuration\n\n";
    section += "A verification configuration exists at `specs/verification.config.ts`.\n";

    // Try to extract key config details
    const config = context.verification.config as {
      messages?: { maxInFlight?: number; maxTabs?: number };
      bounds?: { maxInFlight?: number };
      preset?: string;
      verification?: { timeout?: number; workers?: number };
    };

    if (config.messages || config.bounds) {
      section += "\nKey bounds:\n";
      const maxInFlight = config.messages?.maxInFlight || config.bounds?.maxInFlight;
      if (maxInFlight !== undefined) {
        section += `- maxInFlight: ${maxInFlight}\n`;
      }
      if (config.messages?.maxTabs !== undefined) {
        section += `- maxTabs: ${config.messages.maxTabs}\n`;
      }
    }

    if (config.preset) {
      section += `\nPreset: ${config.preset}\n`;
    }

    if (config.verification) {
      section += "\nVerification settings:\n";
      if (config.verification.timeout !== undefined) {
        section += `- Timeout: ${config.verification.timeout === 0 ? "unlimited" : `${config.verification.timeout}s`}\n`;
      }
      if (config.verification.workers !== undefined) {
        section += `- Workers: ${config.verification.workers}\n`;
      }
    }
  }

  if (context.verification.lastResults) {
    const results = context.verification.lastResults;
    section += "\n### Last Verification Results\n\n";

    if (results.timestamp) {
      section += `Run at: ${results.timestamp.toLocaleString()}\n`;
    }

    if (results.success) {
      section += "\n✓ Verification passed!\n\n";
      if (results.stats) {
        section += `Statistics:
- States generated: ${results.stats.statesGenerated}
- Distinct states: ${results.stats.distinctStates}\n`;
      }
    } else {
      section += "\n✗ Verification failed\n\n";

      if (results.violation) {
        section += `Invariant violated: ${results.violation.name}\n`;
        section += "\nCounterexample trace available.\n";
      }

      if (results.error) {
        section += `Error: ${results.error}\n`;
      }
    }
  }

  return section;
}

/**
 * Generate optimization-focused system prompt
 */
export function generateOptimizationPrompt(context: TeachingContext): string {
  const contexts = Object.entries(context.project.architecture.contexts) as [string, ContextInfo][];
  const allHandlers = contexts.flatMap(([_, ctx]) => ctx.handlers || []);
  const messageFlows = context.project.architecture.messageFlows || [];

  return `You are an expert in formal verification optimization and TLA+ model checking.

# Your Mission

Analyze this Polly project's verification setup and suggest **precise, actionable optimizations**
to reduce verification time while maintaining or improving verification precision.

# Communication Style

- Direct and precise - no fluff
- Always provide concrete, copy-paste-able config changes
- Explain the safety/precision trade-off for each optimization
- Prioritize Tier 1 (safe, no precision loss) optimizations

# Project Context

${generateProjectSection(context, contexts, allHandlers, messageFlows)}

${generateVerificationSection(context)}

# Your Expertise: Optimization Tiers

## Tier 1: Safe Optimizations (ZERO precision loss)

### 1. Message Type Filtering
**Problem**: Analyzers often detect browser events (mousedown, load, install) and other noise
that aren't part of the distributed system being verified, causing exponential state space growth.

**Example Impact**:
- 23 message types (14 noise) with maxInFlight: 2 → timeout after 5 minutes
- 9 relevant message types with maxInFlight: 2 → completes quickly

**Solution**: Add include/exclude filters to config:
\`\`\`typescript
messages: {
  maxInFlight: 2,
  include: ['query', 'command', 'result', ...], // Only protocol messages
  // OR
  exclude: ['load', 'install', 'mousedown', ...],  // Exclude browser events
}
\`\`\`

### 2. Symmetry Reduction
Treat identical or commutative message types as interchangeable to reduce state space.

### 3. Message-Specific Bounds
Different maxInFlight per message type - auth messages should be sequential (1),
but data queries might allow concurrency (3).

### 4. State Abstractions
Abstract implementation details that don't affect correctness properties.

## Tier 2: Controlled Approximations (Minimal, understood precision loss)

### 1. Temporal Constraints
Add known ordering requirements (e.g., "login before other operations").

### 2. Bounded Exploration
Limit depth while ensuring critical paths are covered.

### 3. Incremental Verification
Verify subsystems separately, then compose results.

# Analysis Framework

When analyzing, check:

1. **Message Types**: Are there browser events or UI noise?
2. **State Space**: Current states explored - is it realistic?
3. **Concurrency**: Is maxInFlight uniform when it should be per-message?
4. **Symmetries**: Are there duplicate or commutative message types?
5. **Constraints**: What ordering requirements are implicit?

# Output Format

When user says "analyze", provide:
1. Top 3-5 optimization opportunities (prioritize Tier 1)
2. For each:
   - Tier number
   - Expected impact (e.g., "60% state space reduction")
   - Concrete config diff
   - Safety guarantees or trade-offs

Example format:
\`\`\`
## Optimization 1: Message Type Filtering [Tier 1]

**Impact**: ~60% state space reduction
**Safety**: Zero precision loss - only removes irrelevant messages

**Config Change**:
\`\`\`typescript
messages: {
  maxInFlight: 2,
  include: ['query', 'command', 'result', 'error']
}
\`\`\`

**Rationale**: [Explain based on their actual message types]
\`\`\`

Reference their actual message types, handlers, and flows in your analysis.`;
}
