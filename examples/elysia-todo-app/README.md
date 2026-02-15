# Polly + Elysia Todo App Example

A complete full-stack todo application demonstrating Polly's Elysia middleware integration. This example shows how to build distributed web applications with:

- ✅ **Zero type duplication** - Eden infers types from Elysia automatically
- ✅ **Offline-first** - Automatic request queueing when offline
- ✅ **Real-time sync** - WebSocket broadcast keeps all clients in sync
- ✅ **Authorization** - Route-level auth rules
- ✅ **Client effects** - Declarative client-side state updates
- ✅ **Production-ready** - Minimal overhead with pass-through middleware

## Why This Matters

Modern SPAs are **distributed systems** facing classic problems:
- **CAP theorem** - Must choose consistency vs availability during network partitions
- **Network unreliability** - The first fallacy of distributed computing
- **Cache invalidation** - "One of the two hard things in computer science"
- **Eventual consistency** - State sync across client/server
- **Conflict resolution** - When multiple devices edit offline

The Polly Elysia integration makes these concerns **explicit and verifiable**.

## Project Structure

```
elysia-todo-app/
├── server/               # Elysia API server with Polly middleware
│   └── src/
│       └── index.ts      # Server with polly() middleware
├── client/               # Preact frontend with Eden + Polly wrapper
│   └── src/
│       ├── api.ts        # createPollyClient() wrapper
│       ├── App.tsx       # Todo UI component
│       ├── client.tsx    # Client entry point
│       └── server.tsx    # Dev server (serves client on :5173)
└── package.json          # Workspace root
```

## Installation

From the example root:

```bash
bun install
```

## Running the App

### Start Both Server and Client (Development)

```bash
bun run dev
```

This starts:
- API server on `http://localhost:3000`
- Client dev server on `http://localhost:5173`

### Or Run Separately

**Terminal 1 - API Server:**
```bash
cd server
bun run dev
```

**Terminal 2 - Client:**
```bash
cd client
bun run dev
```

## Development Commands

From the root directory:

```bash
# Development
bun run dev              # Start both server and client
bun run start            # Production start (server only)

# Testing
bun test                 # Run all tests
bun run test:server      # Run server tests only
bun run test:client      # Run client tests only

# Code Quality
bun run lint             # Check code with Biome
bun run lint:fix         # Fix linting issues automatically
bun run format           # Format code with Biome
bun run typecheck        # Type check all packages

# Verification (Formal Methods)
bun run verify           # Generate TLA+ spec and verify
bun run verify:gen       # Generate TLA+ spec only
```

### What Gets Verified?

The `verify` command generates a TLA+ specification from your Polly middleware configuration and checks:

- **Authorization Enforcement**: Unauthenticated users cannot modify todos
- **No Lost Updates**: All operations eventually reach the server
- **Eventual Consistency**: All online clients eventually have the same state
- **Broadcast Delivery**: Updates reach all connected clients

See `server/specs/verification.config.ts` for configuration.

## Features to Try

### 1. Real-Time Synchronization

1. Open `http://localhost:5173` in **multiple browser tabs/windows**
2. Login with username `demo`
3. Add/toggle/delete todos in one tab
4. **Watch them instantly sync to all other tabs!**

This demonstrates:
- WebSocket broadcast from server
- Automatic state synchronization across clients
- Lamport clock ordering

### 2. Offline Support

1. Open DevTools → Network tab
2. Select "Offline" mode
3. Try adding/editing/deleting todos
4. Notice: requests are queued (shown in UI)
5. Go back online → **queued requests automatically replay!**

This demonstrates:
- Automatic offline detection
- Request queueing with optimistic updates
- Retry on reconnection

### 3. Authorization

1. Try to add a todo without logging in
2. Notice: server returns `403 Unauthorized`
3. Login → now todo operations work

This demonstrates:
- Route-level authorization rules
- Authorization enforced before handlers run

### 4. Client Effects

1. Add a todo
2. **No manual state update code needed!**
3. Client state automatically updates via `effects` config

This demonstrates:
- Declarative client-side effects
- Separation of "what happens" from "how to update UI"

## How It Works

### Server: Polly Middleware

```typescript
const app = new Elysia()
  .use(polly({
    state: {
      client: { todos: $syncedState('todos', []) },
      server: { db: $serverState('db', database) },
    },
    effects: {
      'POST /todos': {
        client: ({ result, state }) => {
          state.client.todos.value = [...state.client.todos.value, result];
        },
        broadcast: true,  // Notify all connected clients
      },
    },
    authorization: {
      'POST /todos': ({ state }) => state.client.user.value !== null,
    },
    offline: {
      'POST /todos': {
        queue: true,
        optimistic: (body) => ({ id: -Date.now(), ...body }),
      },
    },
  }))
  .post('/todos', handler, { body: t.Object({ text: t.String() }) });
```

**Key points:**
- **Route pattern matching**: `'POST /todos'`, `'GET /todos/:id'`, `'/todos/*'`
- **Client effects**: Functions that update client state after server operations
- **Broadcast**: WebSocket notification to all connected clients
- **Authorization**: Rules checked before handler execution
- **Offline config**: Queue + optimistic updates

### Client: Eden + Polly Wrapper

```typescript
export const api = createPollyClient<typeof app>('http://localhost:3000', {
  state: clientState,
  websocket: true,
});

// Use it (types inferred from server!)
await api.todos.post({ text: 'Buy milk' });

// Access Polly features
console.log(api.$polly.state.isOnline.value);
console.log(api.$polly.state.queuedRequests.value);
api.$polly.sync();  // Manually sync queued requests
```

**Key points:**
- **Zero duplication**: Types come from server via `typeof app`
- **Offline queue**: Automatic with retry on reconnection
- **WebSocket**: Real-time updates from server
- **State access**: `$polly.state` for connection status and queue

## Development vs Production

### Development Mode

- Middleware adds metadata to responses for debugging
- Client effects serialized from server for hot-reload
- TLA+ generation enabled for verification
- WebSocket enabled by default

### Production Mode

- Middleware is minimal (authorization + broadcast only)
- Client effects are bundled at build time (no serialization)
- Zero overhead from metadata
- WebSocket optional

## Testing Distributed Systems Properties

### Eventual Consistency

1. Go offline in one tab
2. Add 3 todos
3. Go online → should sync to server
4. Check other tabs → todos should appear

**Property**: All online clients eventually have the same state

### Authorization Enforcement

1. Logout
2. Try to add todo → should fail
3. Login → should work

**Property**: Unauthorized requests never reach handlers

### No Lost Updates

1. Open 2 tabs
2. Go offline in both
3. Add different todos in each
4. Go online in both
5. Check server → both todos should exist

**Property**: No updates are lost even with concurrent offline edits

## Next Steps

- **Add TLA+ verification**: Enable `tlaGeneration: true` and verify properties formally
- **Implement CRDTs**: Use Polly's CRDT support for automatic conflict resolution
- **Add persistence**: Connect to a real database (Postgres, SQLite, etc.)
- **Deploy**: Build production bundles and deploy to Fly.io, Railway, etc.

## Architecture Diagram

```
┌─────────────────────────────────────────┐
│          Browser (Client)               │
│  ┌────────────────────────────────────┐ │
│  │ Eden Treaty Client                 │ │ ← Types from server!
│  └──────────┬─────────────────────────┘ │
│             │                            │
│  ┌──────────▼─────────────────────────┐ │
│  │ Polly Wrapper                      │ │
│  │  - Offline queue                   │ │
│  │  - WebSocket connection            │ │
│  │  - Lamport clock sync              │ │
│  └──────────┬─────────────────────────┘ │
│             │                            │
│  ┌──────────▼─────────────────────────┐ │
│  │ Client State ($syncedState)        │ │
│  │  - todos                           │ │
│  │  - user                            │ │
│  └────────────────────────────────────┘ │
└─────────────────┬───────────────────────┘
                  │
        HTTP / WebSocket
                  │
┌─────────────────▼───────────────────────┐
│       Elysia Server (Bun)               │
│  ┌────────────────────────────────────┐ │
│  │ Elysia Routes                      │ │ ← Normal routes!
│  └──────────┬─────────────────────────┘ │
│             │                            │
│  ┌──────────▼─────────────────────────┐ │
│  │ Polly Middleware                   │ │
│  │  - Authorization                   │ │
│  │  - Client effects                  │ │
│  │  - WebSocket broadcast             │ │
│  │  - Offline metadata                │ │
│  └──────────┬─────────────────────────┘ │
│             │                            │
│  ┌──────────▼─────────────────────────┐ │
│  │ Server State ($serverState)        │ │
│  │  - db (in-memory)                  │ │
│  └────────────────────────────────────┘ │
└─────────────────────────────────────────┘
```

## Learn More

- [Polly Documentation](https://github.com/AlexJeffcott/polly)
- [Elysia Documentation](https://elysiajs.com/)
- [Eden Documentation](https://elysiajs.com/eden/overview.html)
- [Distributed Systems Research](../../spa-distributed-systems-research.md)
