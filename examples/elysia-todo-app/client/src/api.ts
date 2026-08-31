import { $syncedState } from "@fairfox/polly";
import { createPollyClient, type PollyClientOptions } from "@fairfox/polly/client";
import type { Signal } from "@preact/signals";
import type { App } from "elysia-todo-app-server/src/index";

type Todo = { id: number; text: string; completed: boolean };
type User = { id: number; username: string };

// Define client state (must match server state keys)
export const clientState = {
  todos: $syncedState<Todo[]>("todos", []),
  user: $syncedState<User | null>("user", null),
};

/**
 * The effect context types shared state as `Signal<unknown>` — polly cannot
 * know an app's shapes — so this app names its own once and reads the context
 * through `appState()`. The server example does the same.
 */
interface AppState {
  client: {
    todos: Signal<Todo[]>;
    user: Signal<User | null>;
  };
}

function appState(state: { client: Record<string, Signal<unknown>> }): AppState {
  return state as unknown as AppState;
}

// Client effects, keyed by the same route patterns the server uses. These are
// imported locally and run after a successful request (online) or on drain
// (offline queue) — handlers are never shipped over the wire.
const clientEffects: PollyClientOptions["clientEffects"] = {
  "POST /todos": ({ result, state }) => {
    const { todos } = appState(state).client;
    todos.value = [...todos.value, result as Todo];
  },
  "PATCH /todos/:id": ({ result, state }) => {
    const { todos } = appState(state).client;
    const updated = result as Todo;
    todos.value = todos.value.map((t) => (t.id === updated.id ? updated : t));
  },
  "DELETE /todos/:id": ({ params, state }) => {
    const { todos } = appState(state).client;
    todos.value = todos.value.filter((t) => t.id !== Number(params.id));
  },
  "POST /auth/login": ({ result, state }) => {
    appState(state).client.user.value = (result as { user: User }).user;
  },
  "POST /auth/logout": ({ state }) => {
    const { todos, user } = appState(state).client;
    user.value = null;
    todos.value = [];
  },
};

// Offline behaviour, mirroring the server `offline` config. Writes attempted
// while offline are queued here (the client cannot fetch server metadata
// offline) and replayed on reconnect.
const offline = {
  "POST /todos": { queue: true },
  "PATCH /todos/:id": { queue: true },
  "DELETE /todos/:id": { queue: true },
} as const;

// Create Polly-enhanced Eden client
// Types are automatically inferred from the server!
export const api = createPollyClient<App>("http://localhost:3000", {
  state: clientState,
  clientEffects,
  offline,
  websocket: process.env.NODE_ENV !== "test", // Enable real-time updates
  onOfflineChange: (isOnline) => {
    console.log(`[Polly] Connection: ${isOnline ? "ONLINE" : "OFFLINE"}`);
  },
});
