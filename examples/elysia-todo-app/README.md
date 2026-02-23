# Elysia Todo App Example

Full-stack todo app with Elysia + Bun. Offline-first, real-time sync via WebSocket, type-safe end-to-end with Eden, and `$resource` for async data fetching.

## What it demonstrates

- Polly Elysia middleware: authorization, client effects, offline queueing, WebSocket broadcast
- `$resource` for tracked async fetching with automatic re-fetch on dependency change
- `$sharedState` with `{ verify: true }` for server-side handler verification
- `requires()` / `ensures()` on state-mutating functions
- Zero type duplication — Eden infers client types from the Elysia server

## Quick start

```bash
bun install
bun run dev
```

This starts the API server on `http://localhost:3000` and the client on `http://localhost:5173`.

Open multiple tabs, log in with any username, and add todos — they sync instantly across all tabs.

## Server: Polly middleware

The middleware declares authorization, effects, and offline behaviour alongside your routes:

```typescript
const app = new Elysia()
  .use(polly({
    state: {
      client: { todos: $syncedState("todos", []), user: $syncedState("user", null) },
      server: { db: $serverState("db", database) },
    },
    effects: {
      "POST /todos": {
        client: ({ result, state }) => {
          state.client.todos.value = [...state.client.todos.value, result];
        },
        broadcast: true,
      },
    },
    authorization: {
      "POST /todos": ({ state }) => state.client.user.value !== null,
    },
    offline: {
      "POST /todos": { queue: true, optimistic: (body) => ({ id: -Date.now(), ...body }) },
    },
  }))
  .post("/todos", handler, { body: t.Object({ text: t.String() }) });
```

## Client: `$resource`

`$resource` fetches data and re-fetches automatically when its dependencies change:

```typescript
const todosResource = $resource("todos", {
  source: () => ({ userId: clientState.user.value?.id ?? null }),
  fetcher: async ({ userId }) => {
    if (userId === null) return [];
    const res = await fetch("http://localhost:3000/todos");
    return res.json();
  },
  initialValue: [],
});
```

Signal reads inside `source` are tracked. The `fetcher` is async and receives the source output — it never reads signals directly, which avoids the broken-tracking problem when `computed()` hits an `await` boundary.

For verification, each `$resource` emits synthetic handlers (`todos_FetchStart`, `todos_FetchSuccess`, `todos_FetchError`) that model the fetch lifecycle as a state machine.

## Verification

State-mutating functions use contracts:

```typescript
export function addTodo(text: string) {
  requires(authState.value.loggedIn === true, "Must be logged in");
  requires(todoCount.value < 100, "Todo limit not reached");
  todoCount.value++;
  ensures(todoCount.value > 0, "Must have at least one todo");
}
```

Run `bun run verify` from the root to generate and check the TLA+ specification.

## File structure

```
server/
  src/
    index.ts                Elysia server with polly() middleware
    state.ts                $sharedState with { verify: true }
    handlers.ts             State mutations with requires/ensures
  specs/
    verification.config.ts  TLA+ verification bounds
client/
  src/
    App.tsx                 Preact todo UI
    api.ts                  createPollyClient wrapping Eden
    todosResource.ts        $resource for async todo fetching
    client.tsx              Browser entry point
    server.tsx              SSR dev server
```

## Next steps

- [webrtc-p2p-chat](../webrtc-p2p-chat/) — peer-to-peer with no server data flow
- [team-task-manager](../team-task-manager/) — end-to-end encryption and local-first collaboration
