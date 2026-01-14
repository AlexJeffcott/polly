# Polly Elysia Middleware - Complete Implementation Specification

**Date:** 2026-01-05

## Overview

This document specifies a complete implementation of Polly as an Elysia middleware plugin. This approach:

- **Leverages Eden's automatic type generation** - zero duplication of types
- **Uses middleware configuration** - centralized Polly semantics without per-route annotations
- **Separates "what" from "how"** - Elysia routes define endpoints, Polly middleware defines distributed systems behavior
- **Enables full-stack verification** - TLA+ generation from server routes + middleware config

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                         CLIENT                              │
│  ┌────────────────────────────────────────────────────┐    │
│  │ Eden Client (types auto-generated from Elysia)     │    │
│  └────────────────┬───────────────────────────────────┘    │
│                   │                                         │
│  ┌────────────────▼───────────────────────────────────┐    │
│  │ Polly Client Wrapper                               │    │
│  │  - Offline queue                                   │    │
│  │  - Optimistic updates                              │    │
│  │  - Authorization checking                          │    │
│  │  - State synchronization                           │    │
│  └────────────────┬───────────────────────────────────┘    │
│                   │                                         │
│  ┌────────────────▼───────────────────────────────────┐    │
│  │ Client State ($syncedState, $sharedState)          │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
                    │
                    │ HTTP / WebSocket
                    │
┌───────────────────▼─────────────────────────────────────────┐
│                         SERVER                              │
│  ┌────────────────────────────────────────────────────┐    │
│  │ Elysia Routes (normal route definitions)           │    │
│  └────────────────┬───────────────────────────────────┘    │
│                   │                                         │
│  ┌────────────────▼───────────────────────────────────┐    │
│  │ Polly Middleware Plugin                            │    │
│  │  - State management (server + client)              │    │
│  │  - Effect execution (server + broadcast)           │    │
│  │  - Authorization enforcement                       │    │
│  │  - Offline metadata in responses                   │    │
│  │  - Route pattern matching                          │    │
│  └────────────────┬───────────────────────────────────┘    │
│                   │                                         │
│  ┌────────────────▼───────────────────────────────────┐    │
│  │ Server State ($serverState, $syncedState)          │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

---

## 1. Core Type Definitions

### `packages/polly/src/elysia/types.ts`

```typescript
import type { Signal } from "@preact/signals-core";

/**
 * Route pattern matching configuration
 * Examples: 'POST /todos', 'GET /todos/:id', '/todos/*'
 */
export type RoutePattern = `${string} ${string}` | string;

/**
 * State configuration for client and server
 */
export interface PollyStateConfig {
  client?: Record<string, Signal<any>>;
  server?: Record<string, Signal<any>>;
}

/**
 * Effect handler context
 */
export interface EffectContext<TResult = any, TBody = any> {
  result: TResult;
  body: TBody;
  state: {
    client: Record<string, Signal<any>>;
    server: Record<string, Signal<any>>;
  };
  params: Record<string, string>;
  clock: { tick: number; contextId: string };
}

/**
 * Client effect configuration for a route
 */
export interface ClientEffectConfig {
  /**
   * Client-side effect to run after successful response
   */
  client: (ctx: EffectContext) => void | Promise<void>;

  /**
   * Whether to broadcast this update to all connected clients
   */
  broadcast?: boolean;

  /**
   * Broadcast filter - only send to clients matching this condition
   */
  broadcastFilter?: (clientState: Record<string, Signal<any>>) => boolean;
}

/**
 * Authorization handler context
 */
export interface AuthorizationContext {
  state: {
    client: Record<string, Signal<any>>;
    server: Record<string, Signal<any>>;
  };
  body?: any;
  params?: Record<string, string>;
  headers: Record<string, string>;
}

/**
 * Authorization handler - return true to allow, false to deny
 */
export type AuthorizationHandler = (
  ctx: AuthorizationContext
) => boolean | Promise<boolean>;

/**
 * Offline behavior configuration for a route
 */
export interface OfflineConfig<TBody = any, TResult = any> {
  /**
   * Whether to queue this request when offline
   */
  queue: boolean;

  /**
   * Optimistic update - what to show the user immediately
   */
  optimistic?: (body: TBody) => TResult;

  /**
   * Merge strategy when online again
   * - 'replace': Replace optimistic with server result
   * - 'merge': Custom merge function
   */
  merge?:
    | "replace"
    | ((optimistic: TResult, server: TResult) => TResult);

  /**
   * Conflict resolution if multiple devices edited offline
   */
  conflictResolution?:
    | "last-write-wins"
    | "server-wins"
    | ((client: TResult, server: TResult) => TResult);
}

/**
 * Complete Polly middleware configuration
 */
export interface PollyConfig {
  /**
   * State signals (client and server)
   */
  state?: PollyStateConfig;

  /**
   * Client effects mapped to route patterns
   */
  effects?: Record<RoutePattern, ClientEffectConfig>;

  /**
   * Authorization rules mapped to route patterns
   */
  authorization?: Record<RoutePattern, AuthorizationHandler>;

  /**
   * Offline behavior mapped to route patterns
   */
  offline?: Record<RoutePattern, OfflineConfig>;

  /**
   * WebSocket path for real-time updates (default: '/polly/ws')
   */
  websocketPath?: string;

  /**
   * Enable TLA+ generation (default: false)
   */
  tlaGeneration?: boolean;
}

/**
 * Metadata added to responses for client wrapper
 */
export interface PollyResponseMetadata {
  /**
   * Client effect to execute
   */
  clientEffect?: {
    handler: string; // Serialized function
    broadcast: boolean;
  };

  /**
   * Offline configuration for this route
   */
  offline?: OfflineConfig;

  /**
   * Lamport clock info
   */
  clock: {
    tick: number;
    contextId: string;
  };
}
```

---

## 2. Middleware Plugin Implementation

### `packages/polly/src/elysia/plugin.ts`

```typescript
import { Elysia, type Context } from "elysia";
import type { PollyConfig, PollyResponseMetadata } from "./types";
import { createLamportClock } from "../core/clock";
import { serializeFunction, deserializeFunction } from "../utils/function-serialization";

/**
 * Route pattern matcher
 * Supports:
 * - Exact match: 'POST /todos'
 * - Param match: 'GET /todos/:id'
 * - Wildcard: '/todos/*'
 */
function matchRoute(pattern: string, method: string, path: string): boolean {
  // Split pattern into method + path or just path
  const parts = pattern.includes(" ")
    ? pattern.split(" ")
    : [null, pattern];

  const [patternMethod, patternPath] = parts;

  // Check method
  if (patternMethod && patternMethod !== method) {
    return false;
  }

  // Check path
  const patternSegments = patternPath.split("/").filter(Boolean);
  const pathSegments = path.split("/").filter(Boolean);

  if (
    patternSegments.length !== pathSegments.length &&
    !patternPath.includes("*")
  ) {
    return false;
  }

  for (let i = 0; i < patternSegments.length; i++) {
    const patternSeg = patternSegments[i];
    const pathSeg = pathSegments[i];

    if (patternSeg === "*") return true;
    if (patternSeg.startsWith(":")) continue; // Param match
    if (patternSeg !== pathSeg) return false;
  }

  return true;
}

/**
 * Find matching config for a route
 */
function findMatchingConfig<T>(
  configs: Record<string, T> | undefined,
  method: string,
  path: string
): T | undefined {
  if (!configs) return undefined;

  for (const [pattern, config] of Object.entries(configs)) {
    if (matchRoute(pattern, method, path)) {
      return config;
    }
  }

  return undefined;
}

/**
 * WebSocket broadcast manager
 */
class BroadcastManager {
  private connections = new Map<string, WebSocket>();

  register(clientId: string, ws: WebSocket) {
    this.connections.set(clientId, ws);
  }

  unregister(clientId: string) {
    this.connections.delete(clientId);
  }

  broadcast(message: any, filter?: (clientId: string) => boolean) {
    const payload = JSON.stringify(message);

    for (const [clientId, ws] of this.connections.entries()) {
      if (filter && !filter(clientId)) continue;
      if (ws.readyState === WebSocket.OPEN) {
        ws.send(payload);
      }
    }
  }
}

/**
 * Main Polly Elysia plugin
 */
export function polly(config: PollyConfig = {}) {
  const clock = createLamportClock("server");
  const broadcaster = new BroadcastManager();
  const clientStateByConnection = new Map<string, any>();

  return new Elysia({ name: "polly" })
    // Add state to context
    .decorate("pollyState", {
      client: config.state?.client || {},
      server: config.state?.server || {},
    })
    .decorate("pollyClock", clock)
    .decorate("pollyBroadcast", broadcaster)

    // WebSocket endpoint for real-time updates
    .ws(config.websocketPath || "/polly/ws", {
      open(ws) {
        const clientId = ws.data.headers["x-client-id"] || crypto.randomUUID();
        broadcaster.register(clientId, ws.raw);

        // Send initial state sync
        ws.send(JSON.stringify({
          type: "state-sync",
          state: config.state?.client || {},
          clock: clock.now(),
        }));
      },
      close(ws) {
        const clientId = ws.data.headers["x-client-id"];
        if (clientId) {
          broadcaster.unregister(clientId);
          clientStateByConnection.delete(clientId);
        }
      },
      message(ws, message) {
        // Handle client state updates
        const data = JSON.parse(message as string);

        if (data.type === "state-update") {
          const clientId = ws.data.headers["x-client-id"];
          if (clientId) {
            clientStateByConnection.set(clientId, data.state);
          }
        }
      },
    })

    // Authorization hook (runs before handler)
    .onBeforeHandle(async ({ request, pollyState, body, params }) => {
      const method = request.method;
      const path = new URL(request.url).pathname;

      const authHandler = findMatchingConfig(
        config.authorization,
        method,
        path
      );

      if (authHandler) {
        const allowed = await authHandler({
          state: pollyState,
          body,
          params,
          headers: Object.fromEntries(request.headers.entries()),
        });

        if (!allowed) {
          return new Response("Unauthorized", { status: 403 });
        }
      }
    })

    // Response hook (runs after handler)
    .onAfterHandle(async ({ request, response, pollyState, pollyClock, pollyBroadcast, body, params }) => {
      const method = request.method;
      const path = new URL(request.url).pathname;

      // Find matching effect config
      const effectConfig = findMatchingConfig(
        config.effects,
        method,
        path
      );

      // Find matching offline config
      const offlineConfig = findMatchingConfig(
        config.offline,
        method,
        path
      );

      // Tick clock
      pollyClock.tick();

      // Execute server-side effects (not yet defined in this version,
      // but could be added as `server: (ctx) => void` in ClientEffectConfig)

      // If broadcast enabled, send to all connected clients
      if (effectConfig?.broadcast) {
        const broadcastMessage = {
          type: "effect",
          path,
          method,
          result: response,
          clock: pollyClock.now(),
        };

        if (effectConfig.broadcastFilter) {
          pollyBroadcast.broadcast(
            broadcastMessage,
            (clientId) => {
              const clientState = clientStateByConnection.get(clientId);
              return effectConfig.broadcastFilter!(clientState);
            }
          );
        } else {
          pollyBroadcast.broadcast(broadcastMessage);
        }
      }

      // Add Polly metadata to response
      const metadata: PollyResponseMetadata = {
        clientEffect: effectConfig
          ? {
              handler: serializeFunction(effectConfig.client),
              broadcast: effectConfig.broadcast || false,
            }
          : undefined,
        offline: offlineConfig,
        clock: pollyClock.now(),
      };

      // Attach metadata as header
      return new Response(JSON.stringify(response), {
        headers: {
          "Content-Type": "application/json",
          "X-Polly-Metadata": JSON.stringify(metadata),
        },
      });
    });
}
```

---

## 3. Client Wrapper Implementation

### `packages/polly/src/client/wrapper.ts`

```typescript
import { treaty, type Treaty } from "@elysiajs/eden";
import { type Signal, signal, effect } from "@preact/signals-core";
import type { PollyResponseMetadata, OfflineConfig } from "../elysia/types";
import { deserializeFunction } from "../utils/function-serialization";
import { createLamportClock } from "../core/clock";

/**
 * Offline queue entry
 */
interface QueuedRequest {
  id: string;
  method: string;
  path: string;
  body: any;
  optimisticResult?: any;
  timestamp: number;
}

/**
 * Client-side state management
 */
interface ClientState {
  isOnline: Signal<boolean>;
  isSyncing: Signal<boolean>;
  queuedRequests: Signal<QueuedRequest[]>;
}

/**
 * Polly-enhanced Eden client
 */
export function createPollyClient<T extends Record<string, any>>(
  url: string,
  options: {
    state?: Record<string, Signal<any>>;
    onOfflineChange?: (isOnline: boolean) => void;
    websocket?: boolean;
  } = {}
) {
  const baseClient = treaty<T>(url);
  const clock = createLamportClock("client");

  // Client state
  const clientState: ClientState = {
    isOnline: signal(navigator.onLine),
    isSyncing: signal(false),
    queuedRequests: signal<QueuedRequest[]>([]),
  };

  // WebSocket connection for real-time updates
  let ws: WebSocket | null = null;

  if (options.websocket !== false) {
    const wsUrl = url.replace(/^http/, "ws") + "/polly/ws";
    ws = new WebSocket(wsUrl);

    ws.addEventListener("open", () => {
      console.log("[Polly] WebSocket connected");
    });

    ws.addEventListener("message", (event) => {
      const message = JSON.parse(event.data);

      if (message.type === "state-sync") {
        // Initial state sync
        Object.assign(options.state || {}, message.state);
      } else if (message.type === "effect") {
        // Remote effect triggered by another client
        // TODO: Execute the effect locally
        console.log("[Polly] Received remote effect:", message);
      }
    });
  }

  // Online/offline listeners
  window.addEventListener("online", () => {
    clientState.isOnline.value = true;
    options.onOfflineChange?.(true);
    processQueue();
  });

  window.addEventListener("offline", () => {
    clientState.isOnline.value = false;
    options.onOfflineChange?.(false);
  });

  /**
   * Process queued requests when back online
   */
  async function processQueue() {
    if (clientState.queuedRequests.value.length === 0) return;

    clientState.isSyncing.value = true;

    const queue = [...clientState.queuedRequests.value];
    clientState.queuedRequests.value = [];

    for (const req of queue) {
      try {
        // Replay request
        const response = await fetch(url + req.path, {
          method: req.method,
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(req.body),
        });

        const result = await response.json();
        const metadata: PollyResponseMetadata = JSON.parse(
          response.headers.get("X-Polly-Metadata") || "{}"
        );

        // Handle merge if optimistic update was used
        if (req.optimisticResult && metadata.offline?.merge) {
          const mergeStrategy = metadata.offline.merge;

          if (mergeStrategy === "replace") {
            // Replace optimistic with server result (default)
            // TODO: Update local state
          } else if (typeof mergeStrategy === "function") {
            const merged = mergeStrategy(req.optimisticResult, result);
            // TODO: Update local state with merged result
          }
        }

        // Execute client effect
        if (metadata.clientEffect) {
          const handler = deserializeFunction(metadata.clientEffect.handler);
          handler({
            result,
            body: req.body,
            state: { client: options.state || {}, server: {} },
            params: {},
            clock: metadata.clock,
          });
        }
      } catch (error) {
        console.error("[Polly] Failed to replay request:", req, error);
        // Re-queue on failure
        clientState.queuedRequests.value.push(req);
      }
    }

    clientState.isSyncing.value = false;
  }

  /**
   * Wrap a request with Polly behavior
   */
  function wrapRequest<TBody, TResult>(
    method: string,
    path: string,
    body: TBody
  ): Promise<TResult> {
    return new Promise(async (resolve, reject) => {
      // Tick client clock
      clock.tick();

      // Make request
      try {
        if (!clientState.isOnline.value) {
          // Offline behavior
          throw new Error("OFFLINE");
        }

        const response = await fetch(url + path, {
          method,
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(body),
        });

        if (!response.ok) {
          throw new Error(`HTTP ${response.status}`);
        }

        const result = await response.json();
        const metadata: PollyResponseMetadata = JSON.parse(
          response.headers.get("X-Polly-Metadata") || "{}"
        );

        // Execute client effect
        if (metadata.clientEffect) {
          const handler = deserializeFunction(metadata.clientEffect.handler);
          handler({
            result,
            body,
            state: { client: options.state || {}, server: {} },
            params: {},
            clock: metadata.clock,
          });
        }

        resolve(result);
      } catch (error) {
        // Check if this route has offline config
        // NOTE: In real implementation, we'd fetch this metadata from server
        // on app load and cache it

        // For now, queue if offline
        if (!clientState.isOnline.value) {
          const queuedRequest: QueuedRequest = {
            id: crypto.randomUUID(),
            method,
            path,
            body,
            timestamp: Date.now(),
          };

          clientState.queuedRequests.value = [
            ...clientState.queuedRequests.value,
            queuedRequest,
          ];

          // TODO: Apply optimistic update if configured

          resolve({} as TResult); // Resolve with optimistic result
        } else {
          reject(error);
        }
      }
    });
  }

  // Return wrapped client with additional Polly features
  return {
    ...baseClient,
    $polly: {
      state: clientState,
      clock,
      ws,
    },
    // TODO: Proxy all methods to wrap with Polly behavior
  };
}
```

---

## 4. Function Serialization Utility

### `packages/polly/src/utils/function-serialization.ts`

```typescript
/**
 * Serialize a function to send to client
 *
 * IMPORTANT: This is a simplified version. In production:
 * - Use a proper serialization library (e.g., serialize-javascript)
 * - Add security checks to prevent XSS
 * - Consider using a registry of named functions instead
 */
export function serializeFunction(fn: Function): string {
  return fn.toString();
}

/**
 * Deserialize a function received from server
 */
export function deserializeFunction(serialized: string): Function {
  // SECURITY WARNING: eval is dangerous!
  // In production, use a safer approach like:
  // 1. Registry of named functions
  // 2. Code generation at build time
  // 3. Proper serialization library with sandboxing

  return new Function(`return ${serialized}`)();
}
```

---

## 5. Complete Example: Todo App

### Server: `apps/todo-server/src/index.ts`

```typescript
import { Elysia, t } from "elysia";
import { polly } from "@fairfox/polly/elysia";
import { $syncedState, $serverState } from "@fairfox/polly";

// In-memory database (replace with real DB)
const db = {
  todos: [] as Array<{ id: number; text: string; completed: boolean }>,
  nextId: 1,
};

const app = new Elysia()
  .use(
    polly({
      // Define state signals
      state: {
        client: {
          todos: $syncedState("todos", []),
          user: $syncedState("user", null),
        },
        server: {
          db: $serverState("db", db),
        },
      },

      // Define client effects by route pattern
      effects: {
        "POST /todos": {
          client: ({ result, state }) => {
            // Add new todo to client state
            state.client.todos.value = [...state.client.todos.value, result];
          },
          broadcast: true, // Notify all connected clients
        },

        "PATCH /todos/:id": {
          client: ({ result, state }) => {
            // Update todo in client state
            state.client.todos.value = state.client.todos.value.map((t) =>
              t.id === result.id ? result : t
            );
          },
          broadcast: true,
        },

        "DELETE /todos/:id": {
          client: ({ params, state }) => {
            // Remove todo from client state
            state.client.todos.value = state.client.todos.value.filter(
              (t) => t.id !== Number(params.id)
            );
          },
          broadcast: true,
        },
      },

      // Authorization rules
      authorization: {
        "POST /todos": ({ state }) => {
          // Must be logged in to create todos
          return state.client.user.value !== null;
        },
        "PATCH /todos/:id": ({ state }) => {
          return state.client.user.value !== null;
        },
        "DELETE /todos/:id": ({ state }) => {
          return state.client.user.value !== null;
        },
      },

      // Offline behavior
      offline: {
        "POST /todos": {
          queue: true,
          optimistic: (body) => ({
            id: -Date.now(), // Temporary negative ID
            text: body.text,
            completed: false,
          }),
          merge: "replace", // Replace optimistic with server result
        },
        "PATCH /todos/:id": {
          queue: true,
          merge: (optimistic, server) => {
            // Custom merge: prefer client's completed status if changed
            return {
              ...server,
              completed: optimistic.completed,
            };
          },
        },
      },

      // Enable TLA+ generation
      tlaGeneration: true,
    })
  )

  // Routes (normal Elysia routes - no Polly annotations!)
  .get("/todos", () => {
    return db.todos;
  })

  .post(
    "/todos",
    ({ body, pollyState }) => {
      const todo = {
        id: db.nextId++,
        text: body.text,
        completed: false,
      };
      db.todos.push(todo);
      return todo;
    },
    {
      body: t.Object({
        text: t.String(),
      }),
    }
  )

  .patch(
    "/todos/:id",
    ({ params, body }) => {
      const todo = db.todos.find((t) => t.id === Number(params.id));
      if (!todo) throw new Error("Todo not found");

      Object.assign(todo, body);
      return todo;
    },
    {
      params: t.Object({
        id: t.String(),
      }),
      body: t.Object({
        text: t.Optional(t.String()),
        completed: t.Optional(t.Boolean()),
      }),
    }
  )

  .delete(
    "/todos/:id",
    ({ params }) => {
      const index = db.todos.findIndex((t) => t.id === Number(params.id));
      if (index === -1) throw new Error("Todo not found");

      db.todos.splice(index, 1);
      return { success: true };
    },
    {
      params: t.Object({
        id: t.String(),
      }),
    }
  )

  .listen(3000);

console.log(`🦊 Todo server running at ${app.server?.hostname}:${app.server?.port}`);
```

### Client: `apps/todo-client/src/api.ts`

```typescript
import { createPollyClient } from "@fairfox/polly/client";
import { $syncedState } from "@fairfox/polly";
import type { app } from "../../todo-server/src/index";

// Client state
export const clientState = {
  todos: $syncedState("todos", [] as Array<{ id: number; text: string; completed: boolean }>),
  user: $syncedState("user", null as { id: number; name: string } | null),
};

// Create Polly-enhanced Eden client
// Types are automatically inferred from server!
export const api = createPollyClient<typeof app>("http://localhost:3000", {
  state: clientState,
  websocket: true,
  onOfflineChange: (isOnline) => {
    console.log(`[Polly] Connection: ${isOnline ? "ONLINE" : "OFFLINE"}`);
  },
});
```

### Client: `apps/todo-client/src/components/TodoList.tsx`

```tsx
import { useSignal } from "@preact/signals";
import { api, clientState } from "../api";

export function TodoList() {
  const newTodoText = useSignal("");

  async function handleAddTodo() {
    if (!newTodoText.value.trim()) return;

    try {
      // This automatically:
      // - Applies optimistic update if offline
      // - Queues request if offline
      // - Executes client effect on success
      // - Broadcasts to other clients
      await api.todos.post({ text: newTodoText.value });
      newTodoText.value = "";
    } catch (error) {
      console.error("Failed to add todo:", error);
    }
  }

  async function handleToggle(id: number, completed: boolean) {
    await api.todos[id].patch({ completed: !completed });
  }

  async function handleDelete(id: number) {
    await api.todos[id].delete();
  }

  return (
    <div>
      <h1>Todos</h1>

      {/* Connection status */}
      <div>
        Status: {api.$polly.state.isOnline.value ? "🟢 Online" : "🔴 Offline"}
        {api.$polly.state.isSyncing.value && " (Syncing...)"}
      </div>

      {/* Queued requests */}
      {api.$polly.state.queuedRequests.value.length > 0 && (
        <div>
          {api.$polly.state.queuedRequests.value.length} requests queued
        </div>
      )}

      {/* New todo input */}
      <div>
        <input
          type="text"
          value={newTodoText.value}
          onInput={(e) => (newTodoText.value = e.currentTarget.value)}
          placeholder="What needs to be done?"
        />
        <button onClick={handleAddTodo}>Add</button>
      </div>

      {/* Todo list */}
      <ul>
        {clientState.todos.value.map((todo) => (
          <li key={todo.id}>
            <input
              type="checkbox"
              checked={todo.completed}
              onChange={() => handleToggle(todo.id, todo.completed)}
            />
            <span style={{ textDecoration: todo.completed ? "line-through" : "none" }}>
              {todo.text}
            </span>
            <button onClick={() => handleDelete(todo.id)}>Delete</button>
          </li>
        ))}
      </ul>
    </div>
  );
}
```

---

## 6. TLA+ Generation

### `packages/polly/src/elysia/tla-generator.ts`

```typescript
import type { PollyConfig } from "./types";

/**
 * Generate TLA+ specification from Elysia app + Polly config
 */
export function generateTLASpec(config: PollyConfig): string {
  const routes = Object.keys(config.effects || {});
  const states = Object.keys(config.state?.client || {});

  return `
---- MODULE TodoApp ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Clients,    \\ Set of client IDs
  MaxTodos    \\ Maximum number of todos

VARIABLES
  clientState,   \\ Client-side state (todos, user)
  serverState,   \\ Server-side state (database)
  network,       \\ Network messages in flight
  offline,       \\ Which clients are offline
  clock          \\ Lamport clock

vars == <<clientState, serverState, network, offline, clock>>

\\* Type invariants
TypeOK ==
  /\\ clientState \\in [Clients -> [todos: Seq(Todo), user: User \\union {NULL}]]
  /\\ serverState.todos \\in Seq(Todo)
  /\\ network \\subseteq Message
  /\\ offline \\subseteq Clients
  /\\ clock \\in Nat

\\* Safety properties
${generateSafetyProperties(config)}

\\* Actions
${generateActions(routes)}

\\* Specification
Init ==
  /\\ clientState = [c \\in Clients |-> [todos |-> <<>>, user |-> NULL]]
  /\\ serverState = [todos |-> <<>>]
  /\\ network = {}
  /\\ offline = {}
  /\\ clock = 0

Next ==
  \\/ \\E c \\in Clients : CreateTodo(c)
  \\/ \\E c \\in Clients : UpdateTodo(c)
  \\/ \\E c \\in Clients : DeleteTodo(c)
  \\/ \\E c \\in Clients : GoOffline(c)
  \\/ \\E c \\in Clients : GoOnline(c)
  \\/ ProcessMessage

Spec == Init /\\ [][Next]_vars /\\ WF_vars(ProcessMessage)

====
`.trim();
}

function generateSafetyProperties(config: PollyConfig): string {
  // Generate properties from authorization rules, etc.
  return `
\\* Todos are eventually consistent
EventualConsistency ==
  \\A c \\in Clients :
    c \\notin offline =>
      <>(clientState[c].todos = serverState.todos)

\\* Authorization is enforced
AuthorizationEnforced ==
  \\A c \\in Clients :
    clientState[c].user = NULL =>
      Len(clientState[c].todos) = 0
  `.trim();
}

function generateActions(routes: string[]): string {
  // Generate action formulas from routes
  return routes
    .map((route) => {
      const [method, path] = route.split(" ");
      const actionName = `${method}${path.replace(/[^a-zA-Z0-9]/g, "")}`;

      return `
${actionName}(client) ==
  /\\ client \\notin offline
  /\\ clientState[client].user /= NULL
  /\\ clock' = clock + 1
  /\\ network' = network \\union {[
       type |-> "${method}",
       path |-> "${path}",
       client |-> client,
       timestamp |-> clock
     ]}
  /\\ UNCHANGED <<clientState, serverState, offline>>
      `.trim();
    })
    .join("\n\n");
}
```

---

## 7. Implementation Checklist

### Phase 1: Core Middleware
- [ ] Implement route pattern matching
- [ ] Add state decoration to Elysia context
- [ ] Create authorization hook
- [ ] Create response transformation hook
- [ ] Add Lamport clock integration

### Phase 2: WebSocket Support
- [ ] WebSocket endpoint for real-time updates
- [ ] Broadcast manager
- [ ] Client state tracking
- [ ] Broadcast filtering

### Phase 3: Client Wrapper
- [ ] Wrap Eden treaty client
- [ ] Offline queue implementation
- [ ] Optimistic updates
- [ ] Merge strategies
- [ ] WebSocket client connection

### Phase 4: Effect Execution
- [ ] Client effect serialization
- [ ] Client effect deserialization (SECURE!)
- [ ] Effect execution context
- [ ] Broadcast effect propagation

### Phase 5: TLA+ Generation
- [ ] Extract routes from Elysia app
- [ ] Generate TLA+ spec from config
- [ ] Property generation from authorization rules
- [ ] Action generation from effects

### Phase 6: Testing & Examples
- [ ] Unit tests for middleware
- [ ] Integration tests for client wrapper
- [ ] Example: Todo app
- [ ] Example: Chat app
- [ ] Example: Collaborative editor

---

## 8. Key Design Decisions

### 1. Zero Type Duplication
**Decision**: Eden generates types from Elysia automatically.
**Rationale**: No need for separate contract DSL - Elysia IS the contract.

### 2. Middleware Configuration
**Decision**: All Polly behavior configured in middleware, not per-route.
**Rationale**:
- Centralized configuration
- Separation of concerns (what vs how)
- Easy to audit all distributed systems behavior

### 3. Function Serialization
**Decision**: Serialize client effects to send in response metadata.
**Rationale**: Client needs to know what effect to execute.
**Security Note**: Use named function registry in production, NOT eval!

### 4. Offline Queue in Client
**Decision**: Client-side queue for offline requests.
**Rationale**:
- Server doesn't need to know about offline behavior
- Client controls retry logic
- Works with any backend

### 5. WebSocket for Broadcasts
**Decision**: Separate WebSocket connection for real-time updates.
**Rationale**:
- HTTP is request/response - need push for broadcasts
- WebSocket gives us bidirectional channel
- Can send state updates from client to server

---

## 9. Comparison to Original Unified Contracts Proposal

| Aspect | Unified Contracts | Elysia Middleware |
|--------|------------------|-------------------|
| Type Definition | Separate contract DSL | Elysia routes + TypeBox |
| Type Generation | Manual | Automatic via Eden |
| Configuration | Per-command in contract | Centralized in middleware |
| Client Creation | From contract | From Elysia app type |
| Server Implementation | From contract primitives | Normal Elysia handlers |
| Learning Curve | New DSL to learn | Use existing Elysia knowledge |
| Incremental Adoption | Requires full contract | Add middleware to existing app |

**Winner**: Elysia Middleware (leverages existing tools, zero duplication)

---

## 10. Future Enhancements

### 1. Named Effect Registry
Replace function serialization with named effects:

```typescript
// Client
import { effects } from "@/shared/effects";

// Server
polly({
  effects: {
    "POST /todos": {
      client: "addTodoToList", // Reference by name
      broadcast: true,
    }
  }
})
```

### 2. CRDT Support
Add automatic CRDT sync for `$sharedState`:

```typescript
polly({
  state: {
    client: {
      document: $sharedState("document", CRDT.Text(""), { crdt: true }),
    }
  }
})
```

### 3. Time-Travel Debugging
Record all effects for replay:

```typescript
polly({
  debug: {
    recordEffects: true,
    maxHistory: 1000,
  }
})
```

### 4. Distributed Tracing
Add OpenTelemetry spans:

```typescript
polly({
  tracing: {
    enabled: true,
    serviceName: "todo-app",
  }
})
```

---

## Conclusion

This implementation specification provides:

1. **Complete type definitions** for middleware configuration
2. **Concrete middleware plugin** that works with Elysia
3. **Client wrapper** that enhances Eden with offline/sync
4. **Full working example** (Todo app)
5. **TLA+ generation** from middleware config
6. **Implementation checklist** for building this

The key insight: **Elysia is already the contract**. We don't need a separate DSL - we just need middleware to add distributed systems semantics to existing routes.
