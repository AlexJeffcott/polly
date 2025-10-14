# Verify Package Generalization Design

## Current State: Web Extension Specific

The verify package currently assumes:
- **Hardcoded contexts**: `{background, content, popup}`
- **Extension-specific concepts**: Tab IDs, Chrome extension architecture
- **Fixed message routing model**: Extension message bus pattern

## Goal: General Message-Passing Verification

Make the verify package work with any message-passing system:
- Actor systems (Akka-style)
- Event buses (Node.js EventEmitter, Redux)
- Worker threads (Web Workers, Node workers)
- Distributed systems (microservices, message queues)
- State machines (XState, etc.)

---

## Architecture: Three-Layer Design

```
┌─────────────────────────────────────────────────────┐
│           User Configuration Layer                  │
│  (defines domain-specific messaging patterns)       │
└─────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────┐
│        Routing Model Adapters (Pluggable)           │
│  • WebExtension  • Actor  • EventBus  • Custom      │
└─────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────┐
│         Core Verification Engine                    │
│  (domain-agnostic TLA+ generation & checking)       │
└─────────────────────────────────────────────────────┘
```

---

## Layer 1: Core Verification Engine (Domain-Agnostic)

### Responsibilities
- Generate TLA+ specs from abstract message-passing models
- Run TLC model checker
- Map violations back to source code
- Provide verification primitives (`before`, `requires`, `ensures`, etc.)

### Abstract Concepts (Universal)
```typescript
interface CoreVerificationModel {
  // Abstract node in the system (context, actor, process, etc.)
  nodes: NodeDefinition[]

  // Message types that flow between nodes
  messageTypes: MessageType[]

  // How messages are routed
  routingRules: RoutingRule[]

  // State that can be mutated
  state: StateSchema

  // Concurrency bounds
  bounds: {
    maxConcurrentMessages: number
    maxNodes: number
  }
}

interface NodeDefinition {
  id: string
  type: string  // "background", "worker", "actor", etc.
  canSendTo: string[]  // Which nodes can this send to?
  canReceiveFrom: string[]
}

interface MessageType {
  name: string
  fields: Record<string, TypeInfo>
  routing: {
    from: string[]  // Which node types can send this?
    to: string[]    // Which node types receive this?
  }
}
```

---

## Layer 2: Routing Model Adapters (Pluggable)

Each adapter translates domain-specific concepts to the core model.

### Example: Web Extension Adapter

```typescript
export class WebExtensionAdapter implements RoutingAdapter {
  name = "web-extension"

  extractModel(codebase: CodebaseAnalysis): CoreVerificationModel {
    return {
      nodes: [
        { id: "background", type: "service-worker", canSendTo: ["*"], canReceiveFrom: ["*"] },
        { id: "content", type: "content-script", canSendTo: ["background", "page"], canReceiveFrom: ["background"] },
        { id: "popup", type: "ui-context", canSendTo: ["background"], canReceiveFrom: ["background"] },
        // ... more contexts
      ],
      messageTypes: this.extractMessageTypes(codebase),
      routingRules: this.inferRoutingFromMessageBus(codebase),
      state: this.extractStateSchema(codebase),
      bounds: {
        maxConcurrentMessages: 6,
        maxNodes: 8  // Fixed set of extension contexts
      }
    }
  }

  // Recognizes `bus.on(type, handler)` pattern
  private inferRoutingFromMessageBus(codebase: CodebaseAnalysis): RoutingRule[] {
    // Extract handlers from bus.on() calls
  }
}
```

### Example: Actor System Adapter

```typescript
export class ActorSystemAdapter implements RoutingAdapter {
  name = "actor-system"

  extractModel(codebase: CodebaseAnalysis): CoreVerificationModel {
    return {
      nodes: this.discoverActors(codebase),  // Dynamic actors
      messageTypes: this.extractMessageTypes(codebase),
      routingRules: [
        { type: "direct", pattern: "actor-to-actor" },
        { type: "supervision", pattern: "parent-to-child" }
      ],
      state: this.extractStateSchema(codebase),
      bounds: {
        maxConcurrentMessages: 10,
        maxNodes: 5  // Finite for model checking
      }
    }
  }

  // Recognizes `actor.send()` or `context.actorOf()` patterns
  private discoverActors(codebase: CodebaseAnalysis): NodeDefinition[] {
    // Find actor definitions
  }
}
```

### Example: Event Bus Adapter

```typescript
export class EventBusAdapter implements RoutingAdapter {
  name = "event-bus"

  extractModel(codebase: CodebaseAnalysis): CoreVerificationModel {
    return {
      nodes: [
        { id: "central-bus", type: "mediator", canSendTo: ["*"], canReceiveFrom: ["*"] },
        ...this.discoverEmitters(codebase)
      ],
      messageTypes: this.extractEventTypes(codebase),
      routingRules: [
        { type: "broadcast", pattern: "one-to-many" }
      ],
      state: this.extractStateSchema(codebase),
      bounds: {
        maxConcurrentMessages: 8,
        maxNodes: 6
      }
    }
  }

  // Recognizes `emitter.on(event, handler)` pattern
  private discoverEmitters(codebase: CodebaseAnalysis): NodeDefinition[] {
    // Find EventEmitter instances
  }
}
```

---

## Layer 3: User Configuration

### Unified Configuration Format

```typescript
// verify.config.ts
import { defineVerification } from '@fairfox/web-ext-verify'
import { WebExtensionAdapter } from '@fairfox/web-ext-verify/adapters/web-extension'

export default defineVerification({
  // 1. Specify the routing model
  adapter: new WebExtensionAdapter({
    // Adapter-specific options
    contexts: ["background", "content", "popup", "options"],
    detectTabBased: true
  }),

  // 2. State bounds (universal)
  state: {
    todos: { maxLength: 10 },
    counter: { min: 0, max: 100 },
    "user.role": { type: "enum", values: ["admin", "user", "guest"] }
  },

  // 3. Concurrency bounds (universal)
  bounds: {
    maxInFlight: 6,
    maxTabs: 2  // Adapter-specific field
  },

  // 4. Verification behavior (universal)
  onBuild: "warn",
  onRelease: "error"
})
```

### Alternative: Actor System Config

```typescript
// verify.config.ts
import { defineVerification } from '@fairfox/web-ext-verify'
import { ActorSystemAdapter } from '@fairfox/web-ext-verify/adapters/actor-system'

export default defineVerification({
  adapter: new ActorSystemAdapter({
    framework: "akka-js",  // or "xstate-actors"
    supervisionStrategy: "restart"
  }),

  state: {
    mailboxSize: { max: 100 },
    activeActors: { max: 5 }
  },

  bounds: {
    maxInFlight: 10,
    maxActors: 5
  }
})
```

---

## Implementation Plan

### Phase 1: Extract Core Engine (Refactor)

**Goal**: Separate domain-agnostic verification from web extension specifics

1. **Create `core/` directory** with:
   - `core/model.ts` - Abstract message-passing model types
   - `core/generator.ts` - TLA+ generation from abstract model
   - `core/primitives.ts` - Universal verification primitives
   - `core/checker.ts` - TLC runner (unchanged)

2. **Move web extension logic** to adapter:
   - `adapters/web-extension/` directory
   - Keep existing extraction logic but adapt interface

### Phase 2: Create Adapter Interface

```typescript
// adapters/base.ts
export interface RoutingAdapter {
  name: string

  // Extract abstract model from codebase
  extractModel(codebase: CodebaseAnalysis): CoreVerificationModel

  // Pattern matchers for code extraction
  recognizeMessageHandler(node: ts.Node): MessageHandler | null
  recognizeStateUpdate(node: ts.Node): StateAssignment | null

  // Optional: Custom TLA+ template extensions
  customInvariants?(): TLAInvariant[]
}
```

### Phase 3: Implement Additional Adapters

**Priority order**:
1. ✅ **WebExtensionAdapter** (refactor existing code)
2. 🎯 **EventBusAdapter** (Node.js EventEmitter, mitt, etc.)
3. 🎯 **WorkerAdapter** (Web Workers, Node worker_threads)
4. 📋 **ActorSystemAdapter** (for XState actors, etc.)
5. 📋 **CustomAdapter** (user-defined patterns)

### Phase 4: Update Configuration System

1. Make `adapter` required field in config
2. Provide default adapter based on project detection:
   - Detects `chrome` API → WebExtensionAdapter
   - Detects `EventEmitter` → EventBusAdapter
   - Detects `Worker` → WorkerAdapter

---

## Benefits of This Design

### 1. **Separation of Concerns**
- Core verification logic is reusable
- Domain knowledge lives in adapters
- Easy to test each layer independently

### 2. **Extensibility**
- Users can write custom adapters
- Community can contribute adapters for popular frameworks
- No changes to core needed for new domains

### 3. **Backward Compatibility**
- Web extension usage remains simple
- Can provide default adapter that "just works"
- Advanced users can customize

### 4. **Clear Boundaries**
```
What's universal?        What's domain-specific?
├─ Message passing       ├─ How messages are sent (bus.on vs actor.send)
├─ State mutations       ├─ Where state lives (background vs actor mailbox)
├─ Concurrency           ├─ What "nodes" are (contexts vs actors)
├─ TLA+ generation       ├─ How to extract patterns from code
└─ Model checking        └─ Domain-specific invariants
```

---

## Example: Using Multiple Adapters

A complex application might use multiple messaging patterns:

```typescript
// verify.config.ts
export default defineVerification({
  // Verify multiple subsystems
  subsystems: [
    {
      name: "extension-core",
      adapter: new WebExtensionAdapter(),
      include: ["src/extension/**/*"]
    },
    {
      name: "worker-pool",
      adapter: new WorkerAdapter(),
      include: ["src/workers/**/*"]
    }
  ],

  // Verify cross-subsystem invariants
  invariants: [
    // Worker messages must complete before extension state updates
    before("WORKER_RESULT", "STATE_UPDATE"),
  ]
})
```

---

## Next Steps

1. **Prototype the core model types** (`core/model.ts`)
2. **Refactor existing TLA+ generator** to use abstract model
3. **Extract WebExtensionAdapter** from current code
4. **Create EventBusAdapter** as second adapter (validation)
5. **Update documentation** with adapter system

---

## Open Questions

1. **How to handle hybrid systems?** (e.g., extension + workers + event bus)
   - Answer: Allow multiple adapters, verify each subsystem separately

2. **Can adapters share common patterns?** (e.g., all use `on(type, handler)`)
   - Answer: Create base adapter classes with shared extraction logic

3. **How to make custom adapters easy?**
   - Answer: Provide template adapter + comprehensive docs + examples

4. **Should adapters be plugins or built-in?**
   - Answer: Core adapters built-in, community adapters as separate packages

---

## Success Criteria

A generalized verify package is successful when:

✅ **New domains can be added without changing core**
✅ **Web extension usage remains simple and familiar**
✅ **Custom adapters are straightforward to write**
✅ **Documentation clearly explains the adapter system**
✅ **Core verification primitives work across all adapters**
