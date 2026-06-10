import { $syncedState } from "@fairfox/polly";
import { createPollyClient } from "@fairfox/polly/client";
import type { App } from "server/src/index";

type Todo = { id: number; text: string; completed: boolean };
type User = { id: number; username: string };

// Define client state (must match server state keys)
export const clientState = {
  todos: $syncedState<Todo[]>("todos", []),
  user: $syncedState<User | null>("user", null),
};

// Client effects, keyed by the same route patterns the server uses. These are
// imported locally and run after a successful request (online) or on drain
// (offline queue) — handlers are never shipped over the wire.
const clientEffects = {
  "POST /todos": ({ result, state }) => {
    state.client.todos.value = [...state.client.todos.value, result as Todo];
  },
  "PATCH /todos/:id": ({ result, state }) => {
    const updated = result as Todo;
    state.client.todos.value = state.client.todos.value.map((t) =>
      t.id === updated.id ? updated : t
    );
  },
  "DELETE /todos/:id": ({ params, state }) => {
    state.client.todos.value = state.client.todos.value.filter((t) => t.id !== Number(params.id));
  },
  "POST /auth/login": ({ result, state }) => {
    state.client.user.value = (result as { user: User }).user;
  },
  "POST /auth/logout": ({ state }) => {
    state.client.user.value = null;
    state.client.todos.value = [];
  },
} as const;

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
  websocket: true, // Enable real-time updates
  onOfflineChange: (isOnline) => {
    console.log(`[Polly] Connection: ${isOnline ? "ONLINE" : "OFFLINE"}`);
  },
});
