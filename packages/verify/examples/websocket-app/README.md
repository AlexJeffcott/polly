# WebSocket Chat + Todo App with Verification

This example demonstrates formal verification for a Bun WebSocket application with **automatic project detection** and **TLA+ template-based verification**.

## Architecture

```
┌─────────────┐
│   Server    │  ← Hub (WebSocket server)
│   (Bun)     │
└──────┬──────┘
       │ broadcasts
       ├──────────────┬──────────────┬───────────
       ▼              ▼              ▼
   ┌────────┐    ┌────────┐    ┌────────┐
   │Client 1│    │Client 2│    │Client N│
   └────────┘    └────────┘    └────────┘

   All clients share:
   - SQLite database (todos, chat messages, users)
   - Global state object (verification tracking)
```

**Hub-and-Spoke Pattern:**
- Clients send messages to the server only
- Server broadcasts updates to all connected clients
- Enables model checking of concurrent access patterns
- WebSocketServer.tla template enforces hub-and-spoke invariants

## Features

### 1. **User Management**
- Join/leave with unique usernames
- Online/offline status tracking
- Connection limits (max 100 concurrent)

### 2. **Chat System**
- Real-time messaging
- Message history (last 100 messages)
- Broadcast to all connected users

### 3. **Todo List**
- Collaborative todo management
- Create, toggle, delete operations
- Shared state across all clients
- Todo limits (max 50)

### 4. **Formal Verification**
- Automatic WebSocket project detection
- Architecture-specific invariants (ServerAlwaysAvailable, ClientsRouteToServer, etc.)
- State bounds enforcement (counts never negative, limits enforced)
- Race condition detection
- Temporal properties (eventual consistency)

## Running the Example

### 1. Start the Server

```bash
cd examples/websocket-app
bun run src/server.ts
```

You should see:
```
🚀 WebSocket Chat + Todo Server

WebSocket:  ws://localhost:3000/ws
Health:     http://localhost:3000/health
Stats:      http://localhost:3000/stats
```

### 2. Run the Test Harness

In another terminal:

```bash
bun run test-harness.ts
```

This simulates:
- 5 concurrent users joining
- Multiple clients creating todos simultaneously
- Chat message flooding
- Race conditions (multiple clients toggling same todo)
- Connection/todo limit testing

### 3. Check Server Health

```bash
curl http://localhost:3000/health
```

Response:
```json
{
  "status": "ok",
  "connections": 5,
  "users": 5,
  "todos": 15,
  "messages": 30
}
```

## Verification

### Running Verification

```bash
# From the websocket-app directory
bunx polly verify
```

Polly will:
1. 🔍 Detect project type: `websocket-app`
2. 📊 Analyze handlers and state types
3. 📝 Generate TLA+ specification with WebSocketServer template
4. ⚙️  Run TLC model checker via Docker
5. ✅ Report verification results

### Verification Configuration

See `specs/verification.config.ts`:

```typescript
import { defineVerification } from "@fairfox/polly-verify"

export default defineVerification({
  messages: {
    maxInFlight: 2,              // Start small for fast verification
    maxClients: 2,               // WebSocket-specific: concurrent clients
    maxMessagesPerClient: 2,
  },

  state: {
    // Connection bounds
    "connections.count": { min: 0, max: 100 },
    "connections.maxConcurrent": { min: 100, max: 100 }, // Constant

    // User bounds
    "users.online": { min: 0, max: 100 },
    "users.total": { min: 0, max: 1000 },

    // Chat bounds
    "chat.messageCount": { min: 0, max: 100 },
    "chat.maxMessages": { min: 100, max: 100 }, // Constant

    // Todo bounds
    "todos.count": { min: 0, max: 50 },
    "todos.completed": { min: 0, max: 50 },
    "todos.maxTodos": { min: 50, max: 50 }, // Constant

    // System state (booleans)
    "system.initialized": { type: "enum", values: ["false", "true"] },
    "system.dbConnected": { type: "enum", values: ["false", "true"] },
  },

  onBuild: "warn",
  onRelease: "error",

  // Custom application invariants
  invariants: [
    {
      name: "ConnectionsWithinLimit",
      expression: "state.connections.count <= state.connections.maxConcurrent",
      description: "Connection count must not exceed maximum",
    },
    {
      name: "OnlineUsersLessOrEqualToConnections",
      expression: "state.users.online <= state.connections.count",
      description: "Online users cannot exceed active connections",
    },
    {
      name: "TodosWithinLimit",
      expression: "state.todos.count <= state.todos.maxTodos",
      description: "Todo count must not exceed maximum",
    },
    {
      name: "CompletedLessOrEqualToTotal",
      expression: "state.todos.completed <= state.todos.count",
      description: "Completed todos cannot exceed total todos",
    },
  ],
})
```

### Architecture-Specific Invariants

The WebSocketServer.tla template automatically enforces:

1. **ServerAlwaysAvailable**
   - Server must never disconnect
   - Catches server crashes or invalid state transitions

2. **ClientsRouteToServer**
   - All client messages must target the server
   - Prevents forbidden direct client-to-client communication

3. **NoClientToClientMessages**
   - Enforces hub-and-spoke topology
   - Clients cannot bypass the server hub

These invariants are automatically included when Polly detects a WebSocket project.

### State Tracking

The application maintains an in-memory state object:

```typescript
export const state: AppState = {
  connections: { count: 0, maxConcurrent: 100 },
  users: { online: 0, total: 0 },
  chat: { messageCount: 0, maxMessages: 100 },
  todos: { count: 0, completed: 0, maxTodos: 50 },
  system: { initialized: false, dbConnected: false },
}
```

This state is:
- Updated atomically by message handlers
- Tracked for verification purposes
- Mirrors database state for consistency checking

### Message Handlers

Handlers follow the `handle*` naming pattern:

```typescript
export function handleUserJoin(username: string): void {
  // Preconditions: System must be initialized
  if (!state.system.initialized) {
    throw new Error("System not initialized")
  }

  if (!username || username.length === 0) {
    throw new Error("Username cannot be empty")
  }

  // Update state
  state.users.online += 1
  state.users.total += 1
  state.connections.count += 1

  // Postconditions: Counts must be consistent
  if (state.users.total < state.users.online) {
    throw new Error("Invariant violation: total < online")
  }
}
```

Polly automatically:
- Detects handlers by pattern matching (`handle*`)
- Extracts message types (handleUserJoin → "USER_JOIN")
- Infers contexts (server-side handlers tagged as "server" context)

## Project Detection

Polly automatically detects this as a WebSocket project by:
1. Finding `package.json` with `bun` as dependency
2. Detecting WebSocket usage patterns in code
3. Identifying hub-and-spoke architecture

This triggers:
- Use of WebSocketServer.tla template
- Generation of `maxClients` configuration
- Context inference for server vs. client handlers

## Testing Race Conditions

The test harness includes race condition scenarios:

### Concurrent Todo Toggling

Multiple clients try to toggle the same todo simultaneously:

```typescript
// All clients toggle the same todo at once
await Promise.all(
  clients.map(client => client.toggleTodo(todoId))
)
```

Verification tests:
- Database transaction isolation
- State consistency under concurrent writes
- Invariant enforcement (completed ≤ count)

### Connection Limit Enforcement

Try to exceed max connections:

```typescript
const MAX_CONNECTIONS = 100
const clients = Array.from({ length: MAX_CONNECTIONS + 5 }, ...)

// Should fail for the extra 5 connections
await Promise.all(clients.map(client => client.join()))
```

The `ConnectionsWithinLimit` invariant detects violations:
```
state.connections.count <= state.connections.maxConcurrent
```

## Files

```
websocket-app/
├── src/
│   ├── types/
│   │   └── state.ts           # AppState type definition
│   ├── handlers.ts            # Message handlers (handle*)
│   └── server.ts              # Bun WebSocket server
├── specs/
│   └── verification.config.ts # Verification configuration
├── test-harness.ts            # Concurrent client simulator
├── tsconfig.json              # TypeScript config
└── README.md                  # This file
```

## Verification Process

1. **Setup** (first time only):
   ```bash
   bunx polly verify --setup
   ```

   Generates `specs/verification.config.ts` with detected state fields and message types.

2. **Configure Bounds**:

   Edit `specs/verification.config.ts` to set appropriate bounds for model checking.

3. **Validate**:
   ```bash
   bunx polly verify --validate
   ```

   Checks configuration for common issues.

4. **Verify**:
   ```bash
   bunx polly verify
   ```

   Generates TLA+ specs and runs model checker.

### What Gets Verified

- ✅ State bounds are never violated (counts stay within min/max)
- ✅ Invariants hold in all reachable states
- ✅ Hub-and-spoke topology is maintained (no client-to-client messages)
- ✅ Server availability (server never disconnects)
- ✅ Message delivery consistency
- ✅ Race conditions are detected (concurrent state mutations)

### Verification Output

Success:
```
✅ Verification passed!
Statistics:
   States explored: 378273
   Distinct states: 184514
```

Failure (shows counterexample):
```
❌ Verification failed!

Invariant violation: TodosWithinLimit

Counterexample trace:
  1. Initial state
  2. handleTodoCreate (state.todos.count = 49)
  3. handleTodoCreate (state.todos.count = 50)
  4. handleTodoCreate (state.todos.count = 51) ← Violation!

Expression: state.todos.count <= state.todos.maxTodos
```

## Performance Tips

For faster verification:
- Start with small bounds (maxClients: 2, maxInFlight: 2)
- Increase bounds incrementally
- Use state constraints to limit state space
- Add custom invariants to detect issues early

Typical verification times:
- Small bounds (2 clients, 2 in-flight): ~5 seconds
- Medium bounds (3 clients, 3 in-flight): ~30 seconds
- Large bounds (5 clients, 5 in-flight): ~5 minutes

## Key Takeaways

1. **Automatic detection** - No manual adapter configuration required
2. **Architecture-specific templates** - WebSocket hub-and-spoke invariants included automatically
3. **Type-driven** - Extracts state and message types from TypeScript
4. **Bounded model checking** - Explores all reachable states within configured bounds
5. **Docker-based** - No TLA+ toolchain installation needed

---

**See also:**
- [Verification Package Documentation](../../README.md)
- [TLA+ Templates](../../specs/tla/templates/)
- [Bun WebSocket API](https://bun.sh/docs/api/websockets)
