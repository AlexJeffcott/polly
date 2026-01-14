# Polly Unified Contracts: Full-Stack Distributed Systems Verification

**Date:** 2026-01-05
**Status:** Proposal
**Related:** [polly-distributed-systems-analysis.md](./polly-distributed-systems-analysis.md), [spa-distributed-systems-research.md](./spa-distributed-systems-research.md)

---

## Executive Summary

This proposal extends Polly to support **full-stack distributed systems** by introducing **unified contracts** that declare the complete behavior of client-server applications. Unified contracts are the single source of truth for:

- State (client and server)
- API operations (commands, queries, subscriptions)
- Effects (how operations modify state)
- Offline behavior (queue, optimistic updates, conflict resolution)
- Authorization rules (who can do what)
- Verification constraints (requires, ensures, invariants)

**Key Insight:** By making the contract contain ALL distributed systems semantics, Polly can:
- Generate fully type-safe clients
- Generate server adapters for any framework (Elysia, Express, etc.)
- Generate mock clients for testing
- Generate TLA+ specifications that verify cross-system properties
- Guarantee consistency between client state and server state

**Philosophy:** Polly is NOT for simple apps. It's for complex distributed systems where **correctness matters more than convenience**.

---

## Problem Statement

### What Polly Currently Solves

Polly currently provides:
1. ✅ Distributed state synchronization across client contexts (Lamport clocks, causal consistency)
2. ✅ Reactive UI updates (Preact Signals)
3. ✅ Formal verification of client-side concurrency (TLA+ generation)
4. ✅ Architecture visualization (Structurizr DSL)

### What Polly Doesn't Solve (Yet)

1. ❌ Client-server protocol verification
2. ❌ Cross-system invariants (e.g., "client's authToken matches server's session")
3. ❌ Offline behavior with server sync
4. ❌ Conflict resolution across multiple clients
5. ❌ Authorization enforcement with verification
6. ❌ Automatic state binding to API calls
7. ❌ Server-side state management

### The Gap

Currently, developers must:
- Manually coordinate between client state and API calls
- Implement offline queuing themselves
- Handle conflict resolution ad-hoc
- Hope authorization is correct
- Cannot verify cross-system properties

**Result:** Even with Polly's client-side verification, the full distributed system (client + server) is unverified.

---

## Solution: Unified Contracts

### Core Concept

A **unified contract** is a declarative specification that describes the entire distributed system:

```typescript
import { $contract, $syncedState, $serverState } from '@fairfox/polly/contract'

export const myApp = $contract({
  // State declarations (client + server)
  state: {
    client: {
      currentUser: $syncedState<User | null>('user', null),
      todos: $syncedState<Todo[]>('todos', []),
      authToken: $sharedState<string | null>('token', null),
    },
    server: {
      sessions: $serverState<Map<string, Session>>('sessions', new Map()),
      database: $serverState<Database>('db', db),
    }
  },

  // API operations with full semantics
  commands: {
    createTodo: {
      // Type contract
      payload: z.object({ text: z.string() }),
      result: z.object({ id: z.number(), text: z.string(), createdAt: z.number() }),

      // Effects: HOW this operation changes the world
      effects: {
        server: async ({ payload, state, user }) => {
          const todo = await state.server.database.value.createTodo({
            text: payload.text,
            userId: user.id,
          })
          return todo
        },
        client: ({ result, state }) => {
          state.client.todos.value = [...state.client.todos.value, result]
        },
        broadcast: true,  // Send to all connected clients
      },

      // Offline behavior
      offline: {
        queue: true,  // Queue if offline
        optimistic: ({ payload, user }) => ({
          id: `temp-${crypto.randomUUID()}`,
          text: payload.text,
          createdAt: Date.now(),
          userId: user.id,
          _syncing: true,
        }),
        merge: ({ optimistic, result }) => result,  // Replace temp with real
      },

      // Authorization
      authorization: ({ state }) => {
        return state.client.authToken.value !== null
      },

      // Verification constraints
      requires: {
        client: 'state.client.authToken.value !== null',
        server: 'state.server.sessions.value.has(request.headers.authorization)',
      },
      ensures: {
        client: 'state.client.todos.value.some(t => t.id === result.id)',
        server: 'state.server.database.value.exists("todos", result.id)',
      },
    }
  },

  queries: {
    getTodos: {
      params: undefined,
      result: z.array(Todo),

      // Can read directly from local state (no server round-trip!)
      strategy: 'local',
      handler: ({ state }) => state.client.todos.value,

      authorization: ({ state }) => state.client.authToken.value !== null,
    }
  },

  subscriptions: {
    'todo-updates': {
      data: z.object({
        type: z.enum(['created', 'updated', 'deleted']),
        todo: Todo,
      }),

      // How subscription updates affect state
      updatesState: ({ data, state }) => {
        switch (data.type) {
          case 'created':
            state.client.todos.value = [...state.client.todos.value, data.todo]
            break
          case 'updated':
            state.client.todos.value = state.client.todos.value.map(t =>
              t.id === data.todo.id ? data.todo : t
            )
            break
          case 'deleted':
            state.client.todos.value = state.client.todos.value.filter(t =>
              t.id !== data.todo.id
            )
            break
        }
      },

      conflictResolution: 'last-write-wins',
    }
  },
})
```

### What Gets Generated

From this single contract, Polly generates:

#### 1. Type-Safe Client
```typescript
import { createClient } from '@fairfox/polly/client'
import { myApp } from './contract'

const client = createClient(myApp, { url: 'localhost:3000' })

// Fully typed, state automatically updated
await client.createTodo({ text: 'Buy milk' })
// todos.value now includes new todo (even if offline!)

// Query local state (no network call)
const todos = await client.getTodos()  // Reads from state.client.todos
```

#### 2. Server Adapter
```typescript
import { elysiaAdapter } from '@fairfox/polly/elysia'
import { myApp } from './contract'

const app = new Elysia()
  .use(elysiaAdapter(myApp))
  .listen(3000)

// Elysia routes automatically created:
// POST /commands/createTodo
// GET /queries/getTodos
// WebSocket /subscriptions (for real-time)

// Authorization, effects, broadcasting all handled automatically
```

#### 3. Mock Client
```typescript
import { createMock } from '@fairfox/polly/mock'
import { myApp } from './contract'

const client = createMock(myApp)

// Same API as real client, but in-memory
// Perfect for tests, Storybook, SSR
await client.createTodo({ text: 'Buy milk' })
```

#### 4. TLA+ Specification
```tla
---- MODULE MyApp ----
EXTENDS Integers, Sequences, FiniteSets

VARIABLES
  \* Client state
  clientTodos,
  clientAuthToken,

  \* Server state
  serverSessions,
  serverDatabase,

  \* Network
  inFlightRequests,

  \* Offline queue
  offlineQueue

\* Client creates todo (online)
ClientCreateTodo ==
  /\ clientAuthToken # NULL  \* From authorization
  /\ \E text \in Strings:
      /\ inFlightRequests' = inFlightRequests \union {[
           type |-> "createTodo",
           payload |-> [text |-> text],
           token |-> clientAuthToken
         ]}
      /\ UNCHANGED <<clientTodos, clientAuthToken, serverSessions, serverDatabase, offlineQueue>>

\* Client creates todo (offline - optimistic)
ClientCreateTodoOffline ==
  /\ clientAuthToken # NULL
  /\ \E text \in Strings:
      /\ LET tempTodo == [id |-> "temp-...", text |-> text, syncing |-> TRUE] IN
         /\ clientTodos' = clientTodos \union {tempTodo}  \* From effects.client
         /\ offlineQueue' = Append(offlineQueue, [type |-> "createTodo", payload |-> [text |-> text]])
         /\ UNCHANGED <<clientAuthToken, inFlightRequests, serverSessions, serverDatabase>>

\* Server processes createTodo
ServerCreateTodo ==
  /\ \E req \in inFlightRequests:
      /\ req.type = "createTodo"
      /\ req.token \in DOMAIN serverSessions  \* From requires.server
      /\ LET newTodo == [id |-> NextId(), text |-> req.payload.text] IN
         /\ serverDatabase' = serverDatabase \union {newTodo}  \* From effects.server
         /\ inFlightRequests' = (inFlightRequests \ {req}) \union {[
              type |-> "createTodoResponse",
              result |-> newTodo
            ]}
         /\ UNCHANGED <<clientTodos, clientAuthToken, serverSessions, offlineQueue>>

\* Client receives response (merge optimistic with real)
ClientReceiveCreateTodo ==
  /\ \E resp \in inFlightRequests:
      /\ resp.type = "createTodoResponse"
      /\ clientTodos' = {t \in clientTodos : ~t.syncing} \union {resp.result}  \* From offline.merge
      /\ inFlightRequests' = inFlightRequests \ {resp}
      /\ UNCHANGED <<clientAuthToken, serverSessions, serverDatabase, offlineQueue>>

\* Cross-system invariants (from ensures)
TodoConsistency ==
  \A todo \in clientTodos:
    todo.syncing \/ (\E t \in serverDatabase : t.id = todo.id)

AuthorizationEnforced ==
  \A req \in inFlightRequests:
    req.type = "createTodo" => req.token \in DOMAIN serverSessions

NoDataLoss ==
  \A cmd \in offlineQueue:
    Eventually(\E todo \in serverDatabase : todo.text = cmd.payload.text)

====
```

#### 5. Architecture Diagrams
```
Generated Structurizr DSL includes:
- Client state components (todos, authToken)
- Server state components (sessions, database)
- Message flows (createTodo: client → server → broadcast)
- Offline queue visualization
- Authorization boundaries
```

---

## Key Design Principles

### 1. Contract Is the Source of Truth

Everything derives from the contract:
- Client behavior
- Server behavior
- Type safety
- Runtime validation
- Verification properties
- Documentation

**No drift possible** - if contract changes, everything changes.

### 2. Effects Are Explicit

Operations declare their effects on state:
```typescript
effects: {
  server: async ({ payload, state }) => {
    // Mutate server state here
    const result = await state.server.database.value.create(payload)
    return result
  },
  client: ({ result, state }) => {
    // Mutate client state here
    state.client.items.value = [...state.client.items.value, result]
  },
  broadcast: true,  // Send to all clients
}
```

**Benefits:**
- TLA+ can model all state transitions
- No hidden side effects
- Verifiable consistency properties

### 3. Offline Is First-Class

Offline behavior is part of the contract:
```typescript
offline: {
  queue: true,           // Can execute offline
  optimistic: (payload) => ({...}),  // Immediate feedback
  merge: (temp, real) => real,       // Reconciliation strategy
}
```

**Benefits:**
- Consistent offline behavior across all operations
- Verifiable "no data loss" properties
- Clear merge semantics

### 4. Authorization Is Verifiable

Authorization rules in contract enable verification:
```typescript
authorization: ({ state, user }) => {
  return state.client.authToken.value !== null
}

requires: {
  server: 'state.server.sessions.value.has(request.token)',
}
```

**TLA+ can prove:** "No unauthorized operations are ever executed"

### 5. State Spans Client and Server

Contracts declare both sides:
```typescript
state: {
  client: { todos: $syncedState('todos', []) },
  server: { database: $serverState('db', db) }
}
```

**Benefits:**
- Verify cross-system invariants
- Prove client-server consistency
- Model full distributed system

---

## Phased Implementation

### Phase 1: Core Contract System (MVP)

**Goal:** Basic contracts with type safety and state synchronization

**Features:**
- Define contracts with state + commands + queries
- Generate type-safe client
- Generate server adapter for Elysia
- Automatic state binding (commands update client state)
- Basic verification (type safety, simple invariants)

**Example:**
```typescript
const app = $contract({
  state: {
    client: { todos: $syncedState<Todo[]>('todos', []) },
    server: { db: $serverState('db', db) }
  },
  commands: {
    createTodo: {
      payload: z.object({ text: z.string() }),
      result: Todo,
      effects: {
        server: async ({ payload, state }) => state.server.db.value.create(payload),
        client: ({ result, state }) => {
          state.client.todos.value = [...state.client.todos.value, result]
        }
      }
    }
  }
})
```

**Deliverables:**
- `@fairfox/polly/contract` - Contract definition DSL
- `@fairfox/polly/client` - Client generation
- `@fairfox/polly/elysia` - Elysia adapter
- Basic TLA+ generation (state + effects)

**Timeline:** 6-8 weeks

### Phase 2: Authorization & Verification

**Goal:** Add authorization rules and enhanced verification

**Features:**
- Authorization rules in contract
- Requires/ensures constraints
- TLA+ verification of authorization (prove no unauthorized access)
- Runtime authorization enforcement

**Example:**
```typescript
commands: {
  deleteTodo: {
    // ... payload, result, effects ...
    authorization: ({ state, payload }) => {
      const todo = state.client.todos.value.find(t => t.id === payload.id)
      return todo?.userId === state.client.currentUser.value?.id
    },
    requires: {
      client: 'state.client.currentUser.value !== null',
      server: 'state.server.sessions.value.has(request.token)',
    },
    ensures: {
      client: '!state.client.todos.value.some(t => t.id === payload.id)',
      server: '!state.server.db.value.exists("todos", payload.id)',
    }
  }
}
```

**Deliverables:**
- Authorization DSL
- Enhanced TLA+ generation (authorization + constraints)
- Runtime authorization middleware

**Timeline:** 4-6 weeks

### Phase 3: Offline Support

**Goal:** Add offline queue, optimistic updates, conflict resolution

**Features:**
- Offline queue configuration
- Optimistic update generation
- Merge strategies
- Conflict resolution policies
- TLA+ verification of offline properties (no data loss, eventual consistency)

**Example:**
```typescript
commands: {
  createTodo: {
    // ... existing ...
    offline: {
      queue: true,
      optimistic: ({ payload }) => ({
        id: `temp-${uuid()}`,
        text: payload.text,
        _syncing: true,
      }),
      merge: ({ optimistic, result }) => result,
    },
    conflictResolution: 'last-write-wins',
  }
}
```

**Deliverables:**
- Offline queue implementation
- Optimistic update system
- Merge/conflict resolution strategies
- Enhanced TLA+ (offline scenarios)

**Timeline:** 6-8 weeks

### Phase 4: Real-Time Subscriptions

**Goal:** WebSocket subscriptions with automatic state updates

**Features:**
- Subscription declarations
- Automatic state updates from subscriptions
- Broadcast to all clients
- Subscription authorization

**Example:**
```typescript
subscriptions: {
  'todo-updates': {
    data: z.object({ type: z.enum(['created', 'updated', 'deleted']), todo: Todo }),
    updatesState: ({ data, state }) => {
      // Automatically update todos based on event
    },
    authorization: ({ state }) => state.client.authToken.value !== null,
  }
}
```

**Deliverables:**
- WebSocket transport
- Subscription system
- Broadcast mechanisms
- TLA+ verification of real-time properties

**Timeline:** 4-6 weeks

### Phase 5: Advanced Features

**Goal:** CRDT support, transactions, advanced conflict resolution

**Features:**
- CRDT integration (Automerge/Yjs)
- Transactional boundaries
- Custom conflict resolution functions
- Multi-step operations
- Saga patterns for distributed transactions

**Timeline:** 8-12 weeks

---

## Technical Architecture

### Contract Definition Layer

```typescript
// packages/polly/src/contract/types.ts

export interface Contract<
  ClientState extends StateDeclaration,
  ServerState extends StateDeclaration,
  Commands extends CommandDeclaration,
  Queries extends QueryDeclaration,
  Subscriptions extends SubscriptionDeclaration
> {
  state: {
    client: ClientState
    server: ServerState
  }
  commands: Commands
  queries: Queries
  subscriptions: Subscriptions
  authorization?: AuthorizationRules
}

export interface CommandDeclaration {
  payload: ZodType<any> | TypeBoxType<any>
  result: ZodType<any> | TypeBoxType<any>
  effects: {
    server: EffectHandler
    client: EffectHandler
    broadcast?: boolean
  }
  offline?: OfflineBehavior
  authorization?: AuthorizationRule
  requires?: ConstraintSet
  ensures?: ConstraintSet
}
```

### Runtime Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     Unified Contract                         │
│  (Single source of truth for entire distributed system)     │
└───────────┬─────────────────────────────────────┬───────────┘
            │                                     │
            ▼                                     ▼
┌───────────────────────┐           ┌───────────────────────┐
│   Client Generation   │           │   Server Adapter      │
│                       │           │                       │
│  • Type-safe client   │           │  • Elysia routes      │
│  • State binding      │           │  • Authorization      │
│  • Offline queue      │           │  • Effect execution   │
│  • Optimistic updates │           │  • Broadcasting       │
└───────────┬───────────┘           └───────────┬───────────┘
            │                                   │
            │         Network (HTTP/WS)         │
            └──────────────┬────────────────────┘
                           │
                           ▼
                  ┌─────────────────┐
                  │  State Manager  │
                  │                 │
                  │  • Lamport clks │
                  │  • Causal order │
                  │  • Conflict res │
                  └─────────────────┘
```

### Code Generation Strategy

```typescript
// packages/polly/src/codegen/client.ts

export function generateClient(contract: Contract): string {
  return `
    export class ${contract.name}Client {
      private state: ClientState
      private transport: Transport
      private offlineQueue: Queue

      ${generateCommands(contract.commands)}
      ${generateQueries(contract.queries)}
      ${generateSubscriptions(contract.subscriptions)}
    }
  `
}

function generateCommands(commands: Commands): string {
  return Object.entries(commands).map(([name, cmd]) => `
    async ${name}(payload: ${cmd.payload.type}): Promise<${cmd.result.type}> {
      // Check authorization
      if (${cmd.authorization}) {
        throw new UnauthorizedError()
      }

      // Check if offline
      if (!this.transport.isOnline() && ${cmd.offline?.queue}) {
        // Generate optimistic result
        const optimistic = ${cmd.offline.optimistic}(payload)

        // Update client state immediately
        ${cmd.effects.client}({ result: optimistic, state: this.state, isOptimistic: true })

        // Queue for later
        this.offlineQueue.push({ command: '${name}', payload })

        return optimistic
      }

      // Online: send to server
      const result = await this.transport.send('${name}', payload)

      // Update client state
      ${cmd.effects.client}({ result, state: this.state, isOptimistic: false })

      return result
    }
  `).join('\n')
}
```

### TLA+ Generation Strategy

```typescript
// packages/polly/src/verify/tla-generator.ts

export function generateTLA(contract: Contract): string {
  return `
---- MODULE ${contract.name} ----
EXTENDS Integers, Sequences, FiniteSets

VARIABLES
  ${generateStateVariables(contract.state)}
  inFlightRequests,
  offlineQueue

${generateCommandOperators(contract.commands)}

${generateInvariants(contract)}

====
  `
}

function generateCommandOperators(commands: Commands): string {
  return Object.entries(commands).map(([name, cmd]) => `
\* Client initiates ${name} (online)
Client${capitalize(name)} ==
  ${cmd.authorization ? `\n  /\\ ${translateToTLA(cmd.authorization)}` : ''}
  ${cmd.requires?.client ? `\n  /\\ ${translateToTLA(cmd.requires.client)}` : ''}
  /\\ \\E payload \in PayloadSpace:
      /\\ inFlightRequests' = inFlightRequests \\union {[
           type |-> "${name}",
           payload |-> payload
         ]}
      /\\ UNCHANGED <<${getUnchangedVars(cmd.effects.client)}>>

\* Server processes ${name}
Server${capitalize(name)} ==
  /\\ \\E req \in inFlightRequests:
      /\\ req.type = "${name}"
      ${cmd.requires?.server ? `\n      /\\ ${translateToTLA(cmd.requires.server)}` : ''}
      /\\ LET result == ${translateEffectToTLA(cmd.effects.server)} IN
         ${generateStateUpdates(cmd.effects.server)}
         /\\ inFlightRequests' = (inFlightRequests \\ {req}) \\union {[
              type |-> "${name}Response",
              result |-> result
            ]}

\* Client receives ${name} response
ClientReceive${capitalize(name)} ==
  /\\ \\E resp \in inFlightRequests:
      /\\ resp.type = "${name}Response"
      ${generateStateUpdates(cmd.effects.client)}
      ${cmd.ensures?.client ? `\n      /\\ ${translateToTLA(cmd.ensures.client)}` : ''}
      /\\ inFlightRequests' = inFlightRequests \\ {resp}
  `).join('\n\n')
}

function generateInvariants(contract: Contract): string {
  const invariants = []

  // Generate from ensures clauses
  Object.entries(contract.commands).forEach(([name, cmd]) => {
    if (cmd.ensures) {
      invariants.push(`
${capitalize(name)}Ensures ==
  ${translateToTLA(cmd.ensures.client)}
  /\\ ${translateToTLA(cmd.ensures.server)}
      `)
    }
  })

  // Authorization invariants
  invariants.push(`
AuthorizationEnforced ==
  \\A req \in inFlightRequests:
    ${Object.entries(contract.commands).map(([name, cmd]) =>
      cmd.authorization ?
        `(req.type = "${name}" => ${translateToTLA(cmd.authorization)})`
        : 'TRUE'
    ).join(' /\\ ')}
  `)

  // Offline invariants
  invariants.push(`
NoDataLoss ==
  \\A cmd \in offlineQueue:
    Eventually(ProcessedOnServer(cmd))
  `)

  return invariants.join('\n\n')
}
```

---

## Integration with Existing Polly Features

### 1. State Primitives

Contracts use existing state primitives:
```typescript
state: {
  client: {
    // Uses existing $syncedState, $sharedState, etc.
    todos: $syncedState<Todo[]>('todos', []),
    token: $sharedState<string | null>('token', null),
  }
}
```

**Benefit:** Leverages existing Lamport clock synchronization, causal ordering.

### 2. Message Bus

Contracts generate message handlers:
```typescript
// Under the hood, Polly generates:
bus.on('createTodo', async (payload) => {
  // Execute effects.server
  const result = await myApp.commands.createTodo.effects.server({ payload, state })

  // Broadcast if configured
  if (myApp.commands.createTodo.effects.broadcast) {
    bus.broadcast('todo-created', result)
  }

  return result
})
```

**Benefit:** Compatible with existing message-based architecture.

### 3. Visualization

Contracts enhance visualization:
```typescript
// polly visualize now shows:
// - Client state components
// - Server state components
// - Command flows (client → server → broadcast)
// - Offline queue
// - Authorization boundaries
```

**Benefit:** Complete architecture documentation.

### 4. Verification

Contracts integrate with existing TLA+ verification:
```typescript
// polly verify analyzes:
// - Existing client-side state machines
// - NEW: Server-side state machines
// - NEW: Cross-system invariants
// - NEW: Offline behavior
// - NEW: Authorization properties
```

**Benefit:** More comprehensive verification.

---

## Example: Authentication + Todo App

### Complete Contract

```typescript
import { $contract, $syncedState, $sharedState, $serverState } from '@fairfox/polly/contract'
import { z } from 'zod'

// Schema definitions
const User = z.object({
  id: z.number(),
  username: z.string(),
  email: z.string(),
})

const Todo = z.object({
  id: z.number(),
  text: z.string(),
  completed: z.boolean(),
  userId: z.number(),
  createdAt: z.number(),
})

const Session = z.object({
  userId: z.number(),
  token: z.string(),
  expiresAt: z.number(),
})

export const todoApp = $contract({
  name: 'TodoApp',

  state: {
    client: {
      currentUser: $syncedState<z.infer<typeof User> | null>('user', null),
      todos: $syncedState<z.infer<typeof Todo>[]>('todos', []),
      authToken: $sharedState<string | null>('token', null),
      offlineQueue: $state<any[]>([]),
      syncStatus: $state<'online' | 'offline' | 'syncing'>('online'),
    },
    server: {
      sessions: $serverState<Map<string, z.infer<typeof Session>>>('sessions', new Map()),
      database: $serverState<Database>('db', db),
    }
  },

  commands: {
    // ============================================================================
    // Authentication
    // ============================================================================

    login: {
      payload: z.object({
        username: z.string(),
        password: z.string(),
      }),
      result: z.object({
        token: z.string(),
        user: User,
      }),

      effects: {
        server: async ({ payload, state }) => {
          // Validate credentials
          const user = await state.server.database.value.validateUser(
            payload.username,
            payload.password
          )

          if (!user) {
            throw new Error('Invalid credentials')
          }

          // Create session
          const token = crypto.randomUUID()
          const session = {
            userId: user.id,
            token,
            expiresAt: Date.now() + 24 * 60 * 60 * 1000, // 24 hours
          }

          state.server.sessions.value.set(token, session)

          return { token, user }
        },

        client: ({ result, state }) => {
          state.client.authToken.value = result.token
          state.client.currentUser.value = result.user
        },

        broadcast: false,
      },

      offline: {
        queue: false,  // Must be online to login
        optimistic: false,
      },

      requires: {
        client: 'state.client.authToken.value === null',
      },

      ensures: {
        client: 'state.client.authToken.value !== null && state.client.currentUser.value !== null',
        server: 'state.server.sessions.value.has(result.token)',
      },
    },

    logout: {
      payload: z.object({}),
      result: z.object({ success: z.boolean() }),

      effects: {
        server: async ({ state, request }) => {
          const token = request.headers.authorization
          state.server.sessions.value.delete(token)
          return { success: true }
        },

        client: ({ state }) => {
          state.client.authToken.value = null
          state.client.currentUser.value = null
          state.client.todos.value = []
        },

        broadcast: false,
      },

      offline: {
        queue: false,
      },

      requires: {
        client: 'state.client.authToken.value !== null',
      },

      ensures: {
        client: 'state.client.authToken.value === null && state.client.currentUser.value === null',
        server: '!state.server.sessions.value.has(request.headers.authorization)',
      },
    },

    // ============================================================================
    // Todo Management
    // ============================================================================

    createTodo: {
      payload: z.object({
        text: z.string().min(1).max(500),
      }),
      result: Todo,

      effects: {
        server: async ({ payload, state, user }) => {
          const todo = await state.server.database.value.createTodo({
            text: payload.text,
            userId: user.id,
            completed: false,
            createdAt: Date.now(),
          })

          return todo
        },

        client: ({ result, state, isOptimistic }) => {
          if (isOptimistic) {
            // Add optimistic todo
            state.client.todos.value = [...state.client.todos.value, result]
          } else {
            // Replace temp with real
            state.client.todos.value = state.client.todos.value.map(t =>
              typeof t.id === 'string' && t.id.startsWith('temp-') && t.text === result.text
                ? result
                : t
            )
          }
        },

        broadcast: true,  // Notify all clients
      },

      offline: {
        queue: true,
        optimistic: ({ payload, user }) => ({
          id: `temp-${crypto.randomUUID()}`,
          text: payload.text,
          completed: false,
          userId: user.id,
          createdAt: Date.now(),
          _syncing: true,
        }),
        merge: ({ optimistic, result }) => result,
      },

      authorization: ({ state }) => {
        return state.client.authToken.value !== null
      },

      requires: {
        client: 'state.client.authToken.value !== null',
        server: 'state.server.sessions.value.has(request.headers.authorization)',
      },

      ensures: {
        client: 'state.client.todos.value.some(t => t.text === payload.text)',
        server: 'state.server.database.value.exists("todos", result.id)',
      },

      conflictResolution: 'last-write-wins',
    },

    updateTodo: {
      payload: z.object({
        id: z.number(),
        text: z.string().min(1).max(500),
        completed: z.boolean(),
      }),
      result: Todo,

      effects: {
        server: async ({ payload, state }) => {
          const todo = await state.server.database.value.updateTodo(payload.id, {
            text: payload.text,
            completed: payload.completed,
          })

          return todo
        },

        client: ({ result, state }) => {
          state.client.todos.value = state.client.todos.value.map(t =>
            t.id === result.id ? result : t
          )
        },

        broadcast: true,
      },

      offline: {
        queue: true,
        optimistic: ({ payload }) => payload,
        merge: ({ optimistic, result }) => result,
      },

      authorization: ({ state, payload }) => {
        const todo = state.client.todos.value.find(t => t.id === payload.id)
        return todo?.userId === state.client.currentUser.value?.id
      },

      requires: {
        client: 'state.client.todos.value.some(t => t.id === payload.id)',
        server: 'state.server.database.value.exists("todos", payload.id)',
      },

      ensures: {
        client: 'state.client.todos.value.find(t => t.id === payload.id).text === payload.text',
        server: 'state.server.database.value.get("todos", result.id).text === result.text',
      },

      conflictResolution: 'crdt',  // Use CRDT for text editing
    },

    deleteTodo: {
      payload: z.object({
        id: z.number(),
      }),
      result: z.object({ success: z.boolean() }),

      effects: {
        server: async ({ payload, state }) => {
          await state.server.database.value.deleteTodo(payload.id)
          return { success: true }
        },

        client: ({ payload, state }) => {
          state.client.todos.value = state.client.todos.value.filter(t => t.id !== payload.id)
        },

        broadcast: true,
      },

      offline: {
        queue: true,
        optimistic: ({ payload }) => ({ success: true }),
        merge: ({ optimistic, result }) => result,
      },

      authorization: ({ state, payload }) => {
        const todo = state.client.todos.value.find(t => t.id === payload.id)
        return todo?.userId === state.client.currentUser.value?.id
      },

      requires: {
        client: 'state.client.todos.value.some(t => t.id === payload.id)',
        server: 'state.server.database.value.exists("todos", payload.id)',
      },

      ensures: {
        client: '!state.client.todos.value.some(t => t.id === payload.id)',
        server: '!state.server.database.value.exists("todos", payload.id)',
      },
    },
  },

  queries: {
    getTodos: {
      params: undefined,
      result: z.array(Todo),

      // Read from local state (no server call)
      strategy: 'local',
      handler: ({ state }) => state.client.todos.value,

      authorization: ({ state }) => state.client.authToken.value !== null,
    },

    getTodo: {
      params: z.object({ id: z.number() }),
      result: Todo,

      strategy: 'local',
      handler: ({ state, params }) => {
        const todo = state.client.todos.value.find(t => t.id === params.id)
        if (!todo) throw new Error('Todo not found')
        return todo
      },

      authorization: ({ state, params }) => {
        const todo = state.client.todos.value.find(t => t.id === params.id)
        return todo?.userId === state.client.currentUser.value?.id
      },
    },
  },

  subscriptions: {
    'todo-updates': {
      data: z.object({
        type: z.enum(['created', 'updated', 'deleted']),
        todo: Todo,
      }),

      updatesState: ({ data, state }) => {
        switch (data.type) {
          case 'created':
            // Only add if not already present (avoid duplicates)
            if (!state.client.todos.value.some(t => t.id === data.todo.id)) {
              state.client.todos.value = [...state.client.todos.value, data.todo]
            }
            break

          case 'updated':
            state.client.todos.value = state.client.todos.value.map(t =>
              t.id === data.todo.id ? data.todo : t
            )
            break

          case 'deleted':
            state.client.todos.value = state.client.todos.value.filter(t =>
              t.id !== data.todo.id
            )
            break
        }
      },

      authorization: ({ state }) => state.client.authToken.value !== null,

      conflictResolution: 'last-write-wins',
    },
  },
})
```

### Client Usage

```typescript
import { createClient } from '@fairfox/polly/client'
import { todoApp } from './contract'

// Create client
const client = createClient(todoApp, {
  url: 'localhost:3000',
  autoConnect: true,
})

// In Polly message bus
bus.on('USER_LOGIN', async ({ username, password }) => {
  try {
    const result = await client.login({ username, password })
    // State automatically updated:
    // - authToken.value = result.token
    // - currentUser.value = result.user

    console.log('Logged in as', result.user.username)
  } catch (error) {
    console.error('Login failed:', error)
  }
})

bus.on('CREATE_TODO', async ({ text }) => {
  // Works offline! Optimistic update shown immediately
  const todo = await client.createTodo({ text })

  // todo is already in todos.value
  // If offline, it has temp ID and will sync later
  console.log('Created todo:', todo)
})

bus.on('UPDATE_TODO', async ({ id, text, completed }) => {
  await client.updateTodo({ id, text, completed })
  // todos.value automatically updated
})

// Query local state (no network call)
bus.on('GET_TODOS', async () => {
  const todos = await client.getTodos()  // Reads from local state
  return todos
})

// Subscribe to updates
await client.subscribe('todo-updates', (data) => {
  // State automatically updated via updatesState handler
  console.log('Todo update:', data.type, data.todo)
})
```

### Server Implementation

```typescript
import { Elysia } from 'elysia'
import { elysiaAdapter } from '@fairfox/polly/elysia'
import { todoApp } from './contract'
import { db } from './database'

const app = new Elysia()
  .use(elysiaAdapter(todoApp, {
    // Optional: customize middleware
    authentication: async (request) => {
      const token = request.headers.authorization
      const session = todoApp.state.server.sessions.value.get(token)

      if (!session || session.expiresAt < Date.now()) {
        throw new Error('Unauthorized')
      }

      return { userId: session.userId }
    },
  }))
  .listen(3000)

console.log('Server running on port 3000')

// Elysia automatically creates:
// POST /commands/login
// POST /commands/logout
// POST /commands/createTodo
// POST /commands/updateTodo
// POST /commands/deleteTodo
// GET /queries/getTodos
// GET /queries/getTodo
// WebSocket /subscriptions
```

### Testing with Mock Client

```typescript
import { createMock } from '@fairfox/polly/mock'
import { todoApp } from './contract'
import { describe, test, expect } from 'bun:test'

describe('Todo App', () => {
  test('create todo when authenticated', async () => {
    const client = createMock(todoApp)

    // Mock initial state
    client.setState({
      client: {
        authToken: 'mock-token',
        currentUser: { id: 1, username: 'alice', email: 'alice@example.com' },
        todos: [],
      }
    })

    // Create todo
    const todo = await client.createTodo({ text: 'Buy milk' })

    // Verify state updated
    const state = client.getState()
    expect(state.client.todos).toHaveLength(1)
    expect(state.client.todos[0].text).toBe('Buy milk')
  })

  test('cannot create todo when not authenticated', async () => {
    const client = createMock(todoApp)

    // No auth token
    client.setState({
      client: {
        authToken: null,
        currentUser: null,
        todos: [],
      }
    })

    // Should throw
    await expect(client.createTodo({ text: 'Buy milk' })).rejects.toThrow('Unauthorized')
  })
})
```

### Verification

```bash
$ polly verify

📊 Analyzing contract: TodoApp

✓ Extracted state:
  - Client: currentUser, todos, authToken
  - Server: sessions, database

✓ Extracted operations:
  - Commands: login, logout, createTodo, updateTodo, deleteTodo
  - Queries: getTodos, getTodo
  - Subscriptions: todo-updates

✓ Generated TLA+ specification (500 lines)

🔍 Running TLC model checker...

✓ Type safety: VERIFIED
✓ Authorization: VERIFIED
  - No unauthorized access to protected operations
  - Users can only modify their own todos

✓ State consistency: VERIFIED
  - Client todos eventually match server database
  - No lost updates in offline scenarios
  - Optimistic updates correctly merged with real results

✓ Offline behavior: VERIFIED
  - All queued operations eventually processed
  - No data loss during network partitions
  - Conflict resolution is deterministic

✓ Cross-system invariants: VERIFIED
  - authToken on client matches session on server
  - Deleted todos removed from both client and server
  - Broadcast updates reach all connected clients

⚠️  1 warning:
  - Command 'updateTodo' uses CRDT conflict resolution but no CRDT implementation specified
    Recommend: Add CRDT library or change to 'last-write-wins'

✅ Verification complete: 12/12 properties verified

State space explored: 1,247,384 states
Model checking time: 2m 34s
```

---

## Migration Path for Existing Polly Apps

### Current Polly App (No Contracts)

```typescript
// State
const todos = $syncedState<Todo[]>('todos', [])
const authToken = $sharedState<string | null>('token', null)

// Message handlers
bus.on('CREATE_TODO', async ({ text }) => {
  const response = await fetch('/api/todos', {
    method: 'POST',
    headers: { Authorization: authToken.value },
    body: JSON.stringify({ text })
  })

  const todo = await response.json()
  todos.value = [...todos.value, todo]
})
```

### Step 1: Extract Contract (Types Only)

```typescript
// contract.ts
export const myApp = $contract({
  state: {
    client: {
      todos: $syncedState<Todo[]>('todos', []),
      authToken: $sharedState<string | null>('token', null),
    },
    // Server state unknown for now
    server: {},
  },

  commands: {
    createTodo: {
      payload: z.object({ text: z.string() }),
      result: Todo,
      // Effects TBD - keep using manual fetch for now
    }
  }
})
```

### Step 2: Use Generated Client

```typescript
import { createClient } from '@fairfox/polly/client'
import { myApp } from './contract'

const client = createClient(myApp, { url: '/api' })

// Replace manual fetch
bus.on('CREATE_TODO', async ({ text }) => {
  const todo = await client.createTodo({ text })
  // State not auto-updated yet - still manual
  todos.value = [...todos.value, todo]
})
```

### Step 3: Add Effects (Auto State Updates)

```typescript
export const myApp = $contract({
  // ... state ...

  commands: {
    createTodo: {
      payload: z.object({ text: z.string() }),
      result: Todo,

      effects: {
        client: ({ result, state }) => {
          state.client.todos.value = [...state.client.todos.value, result]
        }
      }
    }
  }
})

// Now automatic!
bus.on('CREATE_TODO', async ({ text }) => {
  await client.createTodo({ text })
  // todos.value automatically updated
})
```

### Step 4: Add Server Adapter

```typescript
// server.ts
import { elysiaAdapter } from '@fairfox/polly/elysia'
import { myApp } from './contract'

// Add server effects to contract
myApp.commands.createTodo.effects.server = async ({ payload, state }) => {
  return await db.createTodo(payload)
}

// Create server
const app = new Elysia()
  .use(elysiaAdapter(myApp))
  .listen(3000)
```

### Step 5: Add Verification

```typescript
// Add constraints
myApp.commands.createTodo.requires = {
  client: 'state.client.authToken.value !== null',
}

myApp.commands.createTodo.ensures = {
  client: 'state.client.todos.value.some(t => t.text === payload.text)',
}

// Run verification
polly verify
```

**Result:** Gradual migration from unverified manual code to verified unified contract.

---

## Alternatives Considered

### Alternative 1: Split Packages (Already Discussed)

**Rejected because:**
- Harder to verify cross-system properties
- Possible inconsistencies (forgot to bind state)
- Complexity in user code, not framework
- Doesn't optimize for Polly's target use case (complex distributed systems)

### Alternative 2: GraphQL-Style Schema

```graphql
type Todo {
  id: ID!
  text: String!
  completed: Boolean!
}

type Mutation {
  createTodo(text: String!): Todo!
  updateTodo(id: ID!, text: String, completed: Boolean): Todo!
}

type Query {
  todos: [Todo!]!
}
```

**Rejected because:**
- Can't express effects (how state changes)
- Can't express offline behavior
- Can't express authorization logic
- Can't verify (no formal semantics)
- No server-side state modeling

### Alternative 3: tRPC-Style Procedures

```typescript
const appRouter = router({
  createTodo: procedure
    .input(z.object({ text: z.string() }))
    .mutation(async ({ input }) => {
      return await db.createTodo(input)
    })
})
```

**Rejected because:**
- No state declarations
- No client state binding
- No offline support
- No verification
- Request/response only (no subscriptions)

### Alternative 4: Elysia + Eden (Keep Separate)

**Rejected because:**
- Can't verify cross-system properties
- Manual state coordination
- No offline/conflict resolution
- Authorization not verified
- Good for simple APIs, not complex distributed systems

**Unified contracts solve problems none of these address.**

---

## Open Questions & Future Work

### 1. CRDT Integration

**Question:** How to integrate CRDTs (Automerge/Yjs) with contracts?

**Possible approach:**
```typescript
commands: {
  updateText: {
    conflictResolution: 'crdt',
    crdtType: 'text',  // Use Yjs.Text
    crdtLibrary: 'yjs',
  }
}
```

### 2. Multi-Step Operations

**Question:** How to handle operations that span multiple commands?

**Possible approach:**
```typescript
sagas: {
  transferMoney: {
    steps: [
      { command: 'debitAccount', payload: ({ amount, from }) => ({ account: from, amount }) },
      { command: 'creditAccount', payload: ({ amount, to }) => ({ account: to, amount }) },
    ],
    compensations: {
      creditAccount: { command: 'debitAccount' },  // Rollback
    }
  }
}
```

### 3. Rate Limiting & Quotas

**Question:** How to express rate limits in contract?

**Possible approach:**
```typescript
commands: {
  createTodo: {
    rateLimit: {
      requests: 10,
      window: 60000,  // 10 requests per minute
      scope: 'user',
    }
  }
}
```

### 4. Caching Strategies

**Question:** How to express caching beyond local state?

**Possible approach:**
```typescript
queries: {
  getUserProfile: {
    cache: {
      strategy: 'stale-while-revalidate',
      ttl: 3600000,  // 1 hour
      revalidateOn: ['updateProfile'],
    }
  }
}
```

### 5. Database Transactions

**Question:** How to model atomic transactions?

**Possible approach:**
```typescript
commands: {
  transferMoney: {
    effects: {
      server: async ({ payload, state }) => {
        return await state.server.database.value.transaction(async (tx) => {
          await tx.debit(payload.from, payload.amount)
          await tx.credit(payload.to, payload.amount)
        })
      }
    },
    atomicity: 'required',
  }
}
```

---

## Success Criteria

This proposal is successful if:

1. **Verification Works Across Systems**
   - Can prove "client state eventually matches server state"
   - Can prove "no unauthorized operations ever execute"
   - Can prove "offline operations never lost"

2. **Developer Experience Is Acceptable**
   - Contract definition is learnable (< 2 hours to productivity)
   - Contract feels declarative, not imperative
   - Generated code is debuggable

3. **Adoption Increases**
   - Developers choose Polly for complex distributed systems
   - Polly is used in production for mission-critical systems
   - Community contributes server adapters (Express, Fastify, etc.)

4. **Bugs Are Caught**
   - TLA+ verification finds real bugs in contracts
   - Bugs found in verification, not production
   - Developers trust verification results

---

## Conclusion

Unified contracts represent a fundamental shift for Polly:

**From:** Client-side distributed systems framework
**To:** Full-stack distributed systems verification framework

This aligns with Polly's core mission: **Make distributed systems correct by construction.**

By making the contract the single source of truth, we can:
- Generate all artifacts (client, server, mock, TLA+, docs)
- Guarantee consistency (no drift between client and server)
- Verify cross-system properties (authorization, offline, consistency)
- Provide best-in-class DX for complex distributed systems

The complexity is justified because **distributed systems are inherently complex**. The question is where complexity lives:

- ❌ Scattered across user code (hard to verify)
- ✅ Unified in contract (framework handles complexity)

**Recommendation:** Proceed with phased implementation, starting with Phase 1 (Core Contract System) to validate the approach.

---

## Next Steps

1. **Prototype contract DSL** - Build `$contract()` API and validate ergonomics
2. **Implement basic codegen** - Generate simple client from contract
3. **Elysia adapter POC** - Prove server adapter is viable
4. **TLA+ generation** - Extend verifier to handle contracts
5. **Get feedback** - Share with early adopters, iterate on design

---

**Related Documents:**
- [polly-distributed-systems-analysis.md](./polly-distributed-systems-analysis.md) - Analysis of how Polly solves distributed systems problems
- [spa-distributed-systems-research.md](./spa-distributed-systems-research.md) - Research showing SPAs are distributed systems
- [packages/polly/README.md](./packages/polly/README.md) - Current Polly documentation
- [verification/README.md](./verification/README.md) - Current verification system
