# Polly Teach: Interactive Learning for Polly Projects

## Purpose

`polly teach` provides interactive instruction on Polly projects - codebases using Polly for formal verification and architecture analysis. The teaching agent guides users through understanding their project's architecture, verification properties, and Polly's analysis outputs.

## Command Interface

```bash
polly teach
```

The agent inquires about the user's learning objectives and adapts instruction accordingly.

## Teaching Persona

The teaching agent adopts the communication style of an Oxford university professor:
- Direct and precise language
- No emojis or decorative elements
- No florid language or superlatives
- Classic style: clear and simple as truth
- Academic rigor without unnecessary ornamentation

## How It Works

### 1. Analysis

The command uses Polly's existing infrastructure:

```typescript
// Uses vendor/analysis
const analyzer = new ArchitectureAnalyzer(options);
const architecture = await analyzer.analyze();
// Returns: contexts, handlers, message flows, integrations

// Uses vendor/visualize
const visualizer = new StructurizrGenerator();
const diagram = await visualizer.generate(architecture);

// Uses vendor/verify
const verifier = new TLAGenerator();
const spec = await verifier.generate(config, architecture);
```

### 2. Context Preparation

```typescript
export class TeachCommand {
  async execute(): Promise<void> {
    const analysis = await this.analyzeProject();
    const context = this.prepareTeachingContext(analysis);
    this.presentSession(context);
  }

  private async analyzeProject(): Promise<ProjectAnalysis> {
    return {
      architecture: await new ArchitectureAnalyzer(this.options).analyze(),
      visualization: await new StructurizrGenerator().generate(),
      specification: await new TLAGenerator().generate(),
      verification: await this.getVerificationResults(),
    };
  }

  private prepareTeachingContext(analysis: ProjectAnalysis): TeachingContext {
    return {
      project: {
        contexts: analysis.architecture.contexts,
        handlers: analysis.architecture.handlers,
        messageFlows: analysis.architecture.messageFlows,
        integrations: analysis.architecture.integrations,
      },

      polly: {
        architecture: this.explainArchitectureAnalysis(analysis),
        visualization: this.explainVisualization(analysis),
        verification: this.explainVerification(analysis),
      },

      examples: {
        typeScriptHandlers: this.extractHandlerExamples(analysis),
        tlaTranslations: this.extractTLAExamples(analysis),
        properties: this.extractPropertyExamples(analysis),
      },
    };
  }

  private presentSession(context: TeachingContext): void {
    const material = `
# Polly Project Analysis

## Architecture

Your project contains ${context.project.contexts.length} contexts and ${context.project.handlers.length} message handlers.

### Contexts

${context.project.contexts
  .map(
    (c) => `
**${c.name}**
Location: ${c.entryPoint}
Handlers: ${c.handlers.length}
State: ${this.describeState(c.state)}
`
  )
  .join('\n')}

### Message Flows

${this.describeMessageFlows(context.project.messageFlows)}

## Translation Example

Consider this handler from your codebase:

\`\`\`typescript
// ${context.examples.typeScriptHandlers[0].location}
${context.examples.typeScriptHandlers[0].code}
\`\`\`

Polly translates this to TLA+:

\`\`\`tla
${context.examples.tlaTranslations[0].spec}
\`\`\`

The translation preserves the handler's preconditions, state updates, and message semantics.

## Verification

${this.explainVerificationSetup(context)}

---

What would you like to understand?

Possible topics:
- Architecture analysis methodology
- Specific context or handler
- TypeScript to TLA+ translation rules
- Verification properties and their meaning
- Interpreting verification results
- TLA+ specification structure

`;

    console.log(material);
    console.log('\nPrompt: ');
  }
}
```

### 3. System Prompt for Teaching Agent

```typescript
const TEACHING_SYSTEM_PROMPT = `
You are an instructor teaching a developer about their Polly project.

Communication style:
- Direct and precise
- No emojis or decorative elements
- Clear explanations without unnecessary embellishment
- Academic rigor

Context:
${JSON.stringify(teachingContext, null, 2)}

Your role:
1. Help the user understand their project's architecture as analyzed by Polly
2. Explain how Polly's analysis, verification, and visualization work
3. Teach TLA+ concepts using examples from their actual codebase
4. Interpret verification results and suggest improvements

Begin by asking what the user would like to learn about.
`;
```

## Example Sessions

### Session 1: Understanding Architecture Analysis

```
$ polly teach

# Polly Project Analysis

## Architecture

Your project contains 3 contexts and 8 message handlers.

### Contexts

**Server**
Location: src/server/index.ts
Handlers: 3 (query, command, auth)
State: connection map, message queue

**Auth**
Location: src/auth/service.ts
Handlers: 2 (authenticate, validate)
State: user sessions, token store

**Database**
Location: src/db/repository.ts
Handlers: 3 (read, write, delete)
State: data store, transaction log

### Message Flows

Server receives external messages (query, command, auth) via WebSocket.
Query and command messages trigger database operations.
Auth messages flow to Auth context for validation.

## Translation Example

Consider this handler from your codebase:

```typescript
// src/server/handlers.ts:30
export async function handleQuery(message: QueryMessage): Promise<string> {
  const result = await userService.listUsers();
  return JSON.stringify({ type: 'query-result', data: result });
}
```

Polly translates this to TLA+:

```tla
HandleQuery(ctx, msg) ==
  /\ msg.type = "query"
  /\ LET result == ListUsers(contexts[ctx].userService)
     IN /\ contexts' = [contexts EXCEPT
              ![ctx].outbox = Append(@, [
                type |-> "query-result",
                data |-> result
              ])]
```

The translation preserves the handler's preconditions, state updates, and message semantics.

## Verification

Your project defines 2 invariants and 1 temporal property.
Current verification status: all properties verified.

---

What would you like to understand?

Possible topics:
- Architecture analysis methodology
- Specific context or handler
- TypeScript to TLA+ translation rules
- Verification properties and their meaning
- Interpreting verification results
- TLA+ specification structure

Prompt: _
```

User types: "Explain how Polly identifies contexts"

```
Polly identifies contexts through entry point analysis and handler clustering.

## Entry Point Detection

The analyzer begins with files specified in your Polly configuration:

```yaml
verify:
  entryPoints:
    server: src/server/index.ts
    auth: src/auth/service.ts
    database: src/db/repository.ts
```

Each entry point represents a distinct execution context - a logical boundary where state resides and handlers execute.

## Handler Extraction

Within each context, Polly locates message handlers using pattern recognition:

1. Event listener patterns: `emitter.on('message', handler)`
2. Router patterns: `switch(msg.type) { case 'query': ... }`
3. Type guard patterns: `if (isQueryMessage(msg)) { ... }`
4. Handler map patterns: `handlers[msg.type](msg)`

Your server context uses pattern 3:

```typescript
if (isQueryMessage(message)) {
  return await handleQuery(message);
}
```

## State Analysis

For each context, Polly identifies state variables through dataflow analysis:
- Variables modified by handlers
- Persistent data structures
- External state (databases, files)

Your server context maintains:
- `connections: Map<string, WebSocket>` (connection tracking)
- `messageQueue: Message[]` (pending messages)

## Context Boundaries

Contexts communicate through message passing. Polly identifies message flows by tracing:
- Function calls between contexts
- Event emissions
- Message queue operations

In your project, Server sends messages to Database via the `query` channel.

Would you like to explore:
- How specific handlers were identified?
- State analysis methodology?
- Message flow tracing?
- Something else?
```

### Session 2: Understanding TLA+ Translation

```
Prompt: Teach me TLA+ using my code as examples
```

```
I will teach TLA+ through your project's handlers.

## Basic Structure

TLA+ specifications describe state machines. Your TypeScript handlers become TLA+ actions.

Consider your authentication handler:

```typescript
export async function handleAuth(message: AuthMessage): Promise<string> {
  const authenticated = await authService.authenticate(message.token);
  return JSON.stringify({ type: 'auth-result', authenticated });
}
```

This becomes:

```tla
HandleAuth(ctx, msg) ==
  /\ msg.type = "auth"
  /\ LET authenticated == Authenticate(authService, msg.token)
     IN contexts' = [contexts EXCEPT ![ctx].outbox =
          Append(@, [type |-> "auth-result", authenticated |-> authenticated])]
```

## TLA+ Syntax Elements

### Conjunction: `/\`

The `/\` operator means "and". All conditions must hold:

```tla
/\ msg.type = "auth"           \\ Message must be auth type
/\ ctx \in CONTEXTS            \\ Context must be valid
```

### State Updates: Prime Notation

`contexts'` denotes the next state. Unprimed variables reference current state:

```tla
contexts' = [contexts EXCEPT ...]  \\ Next state
```

### Local Definitions: `LET...IN`

Define local values within an expression:

```tla
LET authenticated == Authenticate(...)
IN contexts' = ...
```

### Record Construction

TLA+ records use `|->` for field assignment:

```tla
[type |-> "auth-result", authenticated |-> TRUE]
```

Equivalent to TypeScript: `{ type: "auth-result", authenticated: true }`

### Function Update: `EXCEPT`

Modify one field, preserve others:

```tla
[contexts EXCEPT ![ctx].outbox = Append(@, msg)]
```

Means: update `contexts[ctx].outbox`, keep everything else unchanged.
The `@` symbol represents the current value.

## Type Mappings

Your TypeScript types map to TLA+ as follows:

TypeScript: `type RequestMessage = QueryMessage | CommandMessage | AuthMessage`
TLA+: `MESSAGE_TYPES == {"query", "command", "auth"}`

TypeScript: `interface User { id: string; name: string; }`
TLA+: `[id: STRING, name: STRING]`

TypeScript: `Array<Message>`
TLA+: `Seq(Message)` (sequences are 1-indexed)

## Your Complete Handler

```typescript
export async function routeMessage(message: RequestMessage): Promise<string> {
  if (isQueryMessage(message)) {
    return await handleQuery(message);
  } else if (isCommandMessage(message)) {
    return await handleCommand(message);
  } else if (isAuthMessage(message)) {
    return await handleAuth(message);
  }
  return JSON.stringify({ type: 'error', message: 'Unknown message type' });
}
```

Becomes:

```tla
RouteMessage(ctx, msg) ==
  \/ /\ msg.type = "query"
     /\ HandleQuery(ctx, msg)
  \/ /\ msg.type = "command"
     /\ HandleCommand(ctx, msg)
  \/ /\ msg.type = "auth"
     /\ HandleAuth(ctx, msg)
  \/ /\ msg.type \notin MESSAGE_TYPES
     /\ contexts' = [contexts EXCEPT ![ctx].outbox =
          Append(@, [type |-> "error", message |-> "Unknown message type"])]
```

The `\/` operator means "or" - exactly one branch executes.

What would you like to explore next?
- Specific TLA+ operators
- How preconditions translate
- State invariants
- Temporal properties
- Verification process
```

### Session 3: Understanding Verification Results

```
Prompt: Explain my verification results
```

```
I will explain the verification output for your project.

## Properties Checked

Your specification defines three properties:

### 1. TypeInvariant (Safety)

```tla
TypeInvariant ==
  /\ contexts \in [CONTEXTS -> ContextState]
  /\ \A ctx \in CONTEXTS : contexts[ctx].authenticated \in BOOLEAN
  /\ \A ctx \in CONTEXTS : contexts[ctx].userCount \in Nat
```

This asserts that all state variables maintain correct types.
Status: Verified (no violations in 10,247 states)

### 2. AuthBeforeCommands (Safety)

```tla
AuthBeforeCommands ==
  \A ctx \in CONTEXTS :
    \A msg \in contexts[ctx].inbox :
      msg.type = "command" => contexts[ctx].authenticated = TRUE
```

This requires authentication before command execution.
Status: Verified (no violations in 10,247 states)

### 3. EventualResponse (Liveness)

```tla
EventualResponse ==
  \A msg \in Messages :
    <>(msg \in inbox) => <>(ResponseFor(msg) \in outbox)
```

This ensures every message eventually receives a response.
Status: Verified (checked under weak fairness assumption)

## State Space Exploration

TLC explored 10,247 distinct states in 3 depth levels:
- Initial states: 1
- States at depth 1: 12 (all possible first actions)
- States at depth 2: 156
- States at depth 3: 10,078

No deadlocks found.
No invariant violations.
No temporal property violations.

## What This Means

Your system's specification has been proven correct for all reachable states within the model's parameters.

Current model bounds:
- MAX_MESSAGES = 3
- MAX_USERS = 2
- MESSAGE_TYPES = {"query", "command", "auth"}

To increase confidence, you could:
1. Increase MAX_MESSAGES to explore longer message sequences
2. Add more message types
3. Add symmetry sets to explore larger state spaces efficiently

Would you like to:
- Understand how to add new properties?
- Learn about model bounds and symmetry?
- Examine the TLA+ specification directly?
- Explore what happens if a property fails?
```

## Implementation Structure

```
packages/polly/src/cli/commands/teach/
├── index.ts                    # Command entry point
├── analyzer.ts                 # Wraps existing Polly analyzers
├── context-builder.ts          # Prepares teaching context
├── formatter.ts                # Formats analysis as teaching material
└── prompts.ts                  # System prompts for teaching agent
```

## Key Implementation

```typescript
// packages/polly/src/cli/commands/teach/index.ts
export class TeachCommand {
  async execute(): Promise<void> {
    const analysis = await this.runAnalysis();
    const context = await this.buildTeachingContext(analysis);
    const material = this.formatMaterial(context);

    console.log(material);
    console.log('\nPrompt: ');

    // Claude continues from here with the teaching context
  }

  private async runAnalysis(): Promise<ProjectAnalysis> {
    // Reuse existing analyzers
    const arch = await new ArchitectureAnalyzer(this.config).analyze();
    const viz = await new StructurizrGenerator().generate(arch);
    const spec = await new TLAGenerator().generate(this.config, arch);

    return { architecture: arch, visualization: viz, specification: spec };
  }

  private buildTeachingContext(analysis: ProjectAnalysis): TeachingContext {
    return {
      architecture: {
        summary: this.summarizeArchitecture(analysis.architecture),
        contexts: analysis.architecture.contexts,
        handlers: analysis.architecture.handlers,
        flows: analysis.architecture.messageFlows,
      },
      examples: {
        handlers: this.selectExampleHandlers(analysis.architecture.handlers, 3),
        translations: this.generateTranslationExamples(analysis),
      },
      verification: {
        properties: this.extractProperties(analysis.specification),
        results: await this.getVerificationResults(),
      },
    };
  }

  private formatMaterial(context: TeachingContext): string {
    return `
# Polly Project Analysis

## Architecture

${context.architecture.summary}

### Contexts

${this.formatContexts(context.architecture.contexts)}

### Handlers

${this.formatHandlers(context.handlers)}

## Translation Examples

${this.formatExamples(context.examples)}

## Verification

${this.formatVerification(context.verification)}

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
}
```

## Teaching Scope

The teaching agent covers:

1. **Architecture Analysis**
   - How Polly identifies contexts
   - Handler extraction patterns
   - Message flow tracing
   - State analysis

2. **Visualization**
   - Reading Structurizr diagrams
   - Understanding context relationships
   - Interpreting message flows

3. **Verification**
   - TLA+ fundamentals using project examples
   - TypeScript to TLA+ translation rules
   - Writing properties (invariants, temporal logic)
   - Interpreting TLC output
   - Understanding counterexamples

4. **Project-Specific Guidance**
   - Explaining specific handlers
   - Tracing message flows
   - Suggesting verification properties
   - Identifying architectural patterns

## What It Does Not Cover

- General programming tutorials
- Non-Polly projects
- Features unrelated to formal verification
- Detailed TypeScript language features (unless relevant to translation)

## Configuration

Optional configuration in `.polly/config.yaml`:

```yaml
teach:
  examples:
    maxHandlers: 3              # Number of example handlers to show
    includeGenerated: false     # Show generated TLA+ in full

  interaction:
    verbosity: normal           # concise | normal | detailed
```

The teaching agent uses this configuration to adjust example complexity and explanation depth.
