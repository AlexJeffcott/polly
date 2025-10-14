# WebSocket Chat + Todo App with Verification

This example demonstrates formal verification for a Bun WebSocket application using **Eden types** for end-to-end type safety and **SQLite** for shared state management.

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

### 4. **Verification**
- State invariants (counts never negative, limits enforced)
- Preconditions/postconditions on handlers
- Temporal properties (eventual consistency)
- Race condition detection

## Type Safety with Eden

This example uses [Elysia](https://elysiajs.com/) Eden types for compile-time type safety:

```typescript
// Define message schema
export const ClientMessageSchema = t.Union([
  t.Object({
    type: t.Literal("USER_JOIN"),
    payload: t.Object({ username: t.String() }),
  }),
  t.Object({
    type: t.Literal("CHAT_SEND"),
    payload: t.Object({ text: t.String() }),
  }),
  // ... more message types
])

export type ClientMessage = Static<typeof ClientMessageSchema>
```

**Benefits:**
- Full type inference from schema to handlers
- Runtime validation (optional)
- Compile-time errors for invalid message shapes
- Documentation via types

**Does Eden change verification?**
No. The verification system extracts types from your TypeScript code statically. Eden provides runtime type checking and compile-time safety, but doesn't fundamentally change how verification works. The adapter still recognizes handlers by pattern (`handle*` functions) and extracts verification primitives (`requires()`, `ensures()`).

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

This will simulate:
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

### 4. View State

```bash
curl http://localhost:3000/stats
```

## Verification

### State Tracking

The application maintains an in-memory state object that mirrors database state for verification:

```typescript
export const state: AppState = {
  connections: { count: 0, maxConcurrent: 100 },
  users: { online: 0, total: 0 },
  chat: { messageCount: 0, maxMessages: 100 },
  todos: { count: 0, completed: 0, maxTodos: 50 },
  system: { initialized: false, dbConnected: false },
}
```

### Verification Primitives

All handlers use `requires()` and `ensures()` to verify state consistency:

```typescript
export function handleUserJoin(ctx: HandlerContext, message: ClientMessage): void {
  requires(state.system.initialized === true, "System must be initialized")
  requires(message.payload.username.length > 0, "Username cannot be empty")
  requires(message.payload.username.length <= 20, "Username too long")

  // ... handler logic ...

  ensures(state.users.online > 0, "Must have online users")
  ensures(state.users.total >= state.users.online, "Total >= online")
}
```

### Custom Invariants

The WebSocketAdapter defines WebSocket-specific invariants:

```typescript
customInvariants(): Array<[name: string, tlaExpression: string]> {
  return [
    [
      "ServerAlwaysAvailable",
      'ports["server"] = "connected"'
    ],
    [
      "ClientsConnectToServer",
      "\\A msg \\in Range(messages) : " +
      '(msg.source # "server") => ("server" \\in msg.targets)'
    ],
    [
      "BroadcastConsistency",
      "\\A c1, c2 \\in Contexts : " +
      '(c1 # "server" /\\ c2 # "server") => ' +
      "\\* All connected clients eventually receive broadcasts"
    ],
  ]
}
```

### Verification Config

See `verification.config.ts` for the complete configuration:

```typescript
export default defineVerification({
  adapter: new WebSocketAdapter({
    tsConfigPath: "./tsconfig.json",
    useEdenTypes: true,
    handlerPattern: /^handle[A-Z]/,
    maxConnections: 10, // Model check with 10 clients
    maxInFlight: 5,
  }),

  state: {
    "connections.count": { type: "range", min: 0, max: 100 },
    "users.online": { type: "range", min: 0, max: 100 },
    // ... more state bounds
  },

  invariants: {
    TodosWithinLimit: "state.todos.count <= state.todos.maxTodos",
    CompletedLessOrEqualToTotal: "state.todos.completed <= state.todos.count",
    // ... more invariants
  },
})
```

## Adapter Implementation

The `WebSocketAdapter` recognizes:

1. **Handler Functions**: Functions matching `/^handle[A-Z]/`
   - `handleUserJoin` → `USER_JOIN` message type
   - Converts PascalCase to SCREAMING_SNAKE_CASE

2. **State Mutations**: Assignments to `state.*` properties
   ```typescript
   state.users.online += 1  // Recognized
   ```

3. **Verification Conditions**: `requires()` and `ensures()` calls
   ```typescript
   requires(state.todos.count < state.todos.maxTodos, "Too many todos")
   ```

4. **Hub-and-Spoke Topology**:
   - 1 server node (can send/receive from all)
   - N client nodes (can only send/receive from server)

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

This tests:
- Database transaction isolation
- State consistency under concurrent writes
- Verification constraint enforcement

### Connection Limit Enforcement

Try to exceed max connections:

```typescript
const MAX_CONNECTIONS = 100
const clients = Array.from({ length: MAX_CONNECTIONS + 5 }, ...)

// Should fail for the extra 5 connections
await Promise.all(clients.map(client => client.join()))
```

Verification ensures:
```typescript
ensures(
  state.connections.count <= state.connections.maxConcurrent,
  "Must not exceed max connections"
)
```

## Comparison with Other Adapters

### WebExtension Adapter
- **Topology**: Multiple contexts (background, content, popup, devtools)
- **Routing**: Chrome message passing API
- **Recognition**: `chrome.runtime.onMessage` listeners

### EventBus Adapter
- **Topology**: Single process, multiple handlers
- **Routing**: Event emitter pattern
- **Recognition**: `.on()` / `.addEventListener()` registrations

### WebSocket Adapter
- **Topology**: Hub-and-spoke (server + clients)
- **Routing**: WebSocket broadcast pattern
- **Recognition**: `handle*` function pattern
- **Unique**: Eden type integration, SQLite state management

## Files

```
websocket-app/
├── src/
│   ├── types.ts         # Eden type schemas
│   ├── db.ts            # SQLite operations
│   ├── handlers.ts      # Message handlers with verification
│   └── server.ts        # Bun WebSocket server
├── test-harness.ts      # Concurrent client simulator
├── verification.config.ts # Verification configuration
├── tsconfig.json        # TypeScript config
└── README.md            # This file
```

## Next Steps

1. **Generate TLA+ Spec**: Run the verification tool to generate TLA+ specification
2. **Model Check**: Use TLC to verify properties
3. **Add More Handlers**: Extend with additional message types
4. **Stress Test**: Increase client count in test harness
5. **Custom Invariants**: Add domain-specific verification conditions

## Key Takeaways

1. **Eden types provide compile-time safety** but don't change verification
2. **Hub-and-spoke pattern** enables bounded model checking of concurrent access
3. **Verification primitives** ensure state consistency across database operations
4. **Test harness** demonstrates race conditions and limit enforcement
5. **Adapter system** generalizes to any message-passing paradigm

---

**See also:**
- [Verification Package Documentation](../../README.md)
- [WebSocketAdapter Implementation](../../src/adapters/websocket/index.ts)
- [Elysia Eden Types](https://elysiajs.com/eden/overview.html)
- [Bun WebSocket API](https://bun.sh/docs/api/websockets)
