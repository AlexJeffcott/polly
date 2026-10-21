import { cors } from "@elysiajs/cors";
import { $serverState, $syncedState } from "@fairfox/polly";
import { polly } from "@fairfox/polly/elysia";
import { type Signal, signal } from "@preact/signals-core";
import { Elysia, t } from "elysia";
import { addTodo, login, logout, removeTodo } from "./handlers";

// Simple in-memory database
interface Todo {
  id: number;
  text: string;
  completed: boolean;
}

interface User {
  id: number;
  username: string;
}

const db = {
  todos: signal<Todo[]>([]),
  users: signal<User[]>([{ id: 1, username: "demo" }]),
  nextTodoId: 1,
};

/**
 * Polly's Elysia plugin cannot know an app's state shapes, so it types shared
 * state as `Signal<unknown>` — on `pollyState` in a route handler and on
 * `state` in an effect. This app names its own shapes once, here, and reads
 * that state through `appState()` rather than asserting at each use.
 */
interface AppState {
  client: {
    todos: Signal<Todo[]>;
    user: Signal<User | null>;
  };
  server: {
    db: Signal<typeof db>;
    session: Signal<User | null>;
  };
}

function appState(state: {
  client: Record<string, Signal<unknown>>;
  server: Record<string, Signal<unknown>>;
}): AppState {
  return state as unknown as AppState;
}

// Polly-enhanced Elysia app. `index.ts` listens on it; tests drive it in
// process through Eden, without a port.
export const app = new Elysia()
  .use(cors())
  .use(
    polly({
      // Define shared state (client + server)
      state: {
        client: {
          todos: $syncedState<Todo[]>("todos", []),
          user: $syncedState<User | null>("user", null),
        },
        server: {
          db: $serverState("db", db),
          // Who is logged in, as the server knows it. The login route sets
          // it and authorization reads it. `client.user` is client state:
          // the client's login effect sets it in the browser, and nothing
          // ever writes the server's copy.
          session: $serverState<User | null>("session", null),
        },
      },

      // Define client-side effects
      effects: {
        "POST /todos": {
          client: ({ result, state }) => {
            // Add new todo to client state
            const { todos } = appState(state).client;
            todos.value = [...todos.value, result as Todo];
          },
          broadcast: true, // Notify all connected clients
        },

        "PATCH /todos/:id": {
          client: ({ result, state }) => {
            // Update specific todo in client state
            const { todos } = appState(state).client;
            const updated = result as Todo;
            todos.value = todos.value.map((t) => (t.id === updated.id ? updated : t));
          },
          broadcast: true,
        },

        "DELETE /todos/:id": {
          client: ({ params, state }) => {
            // Remove todo from client state
            const { todos } = appState(state).client;
            todos.value = todos.value.filter((t) => t.id !== Number(params.id));
          },
          broadcast: true,
        },

        "POST /auth/login": {
          client: ({ result, state }) => {
            // Set logged-in user
            appState(state).client.user.value = (result as { user: User }).user;
          },
          broadcast: false, // Don't broadcast auth changes
        },

        "POST /auth/logout": {
          client: ({ state }) => {
            // Clear user
            state.client.user.value = null;
            state.client.todos.value = [];
          },
          broadcast: false,
        },
      },

      // Authorization rules
      // Authorization rules, checked against server state. This demo keeps
      // one server-wide session; a real app would resolve the caller from a
      // token in `headers`.
      authorization: {
        "POST /todos": ({ state }) => appState(state).server.session.value !== null,
        "PATCH /todos/:id": ({ state }) => appState(state).server.session.value !== null,
        "DELETE /todos/:id": ({ state }) => appState(state).server.session.value !== null,
      },

      // Offline behavior
      offline: {
        "POST /todos": {
          queue: true, // Queue when offline
          optimistic: (body) => ({
            id: -Date.now(), // Temporary negative ID
            text: (body as { text: string }).text,
            completed: false,
          }),
        },
        "PATCH /todos/:id": {
          queue: true,
        },
        "DELETE /todos/:id": {
          queue: true,
        },
      },

      // Enable TLA+ generation for verification
      tlaGeneration: true,
    })
  )

  // Authentication endpoints
  .post(
    "/auth/login",
    ({ body, pollyState }) => {
      const user = db.users.value.find((u) => u.username === body.username);
      if (!user) {
        throw new Error("User not found");
      }
      // Track auth state for verification
      login(user.username);
      appState(pollyState).server.session.value = user;
      return { user, token: "demo-token" };
    },
    {
      body: t.Object({
        username: t.String(),
      }),
    }
  )

  .post("/auth/logout", ({ pollyState }) => {
    // Track auth state for verification
    logout();
    appState(pollyState).server.session.value = null;
    return { success: true };
  })

  // Todo endpoints
  .get("/todos", ({ pollyState }) => {
    return appState(pollyState).server.db.value.todos.value;
  })

  .post(
    "/todos",
    ({ body, pollyState }) => {
      // Track todo count for verification
      addTodo(body.text);

      const store = appState(pollyState).server.db.value;
      const todo: Todo = {
        id: store.nextTodoId++,
        text: body.text,
        completed: false,
      };

      store.todos.value = [...store.todos.value, todo];

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
    ({ params, body, pollyState }) => {
      const store = appState(pollyState).server.db.value;
      const todos = store.todos.value;
      const todo = todos.find((t) => t.id === Number(params.id));

      if (!todo) {
        throw new Error("Todo not found");
      }

      // Update todo
      Object.assign(todo, body);

      // Trigger reactivity
      store.todos.value = [...todos];

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
    ({ params, pollyState }) => {
      const store = appState(pollyState).server.db.value;
      const todos = store.todos.value;
      const index = todos.findIndex((t) => t.id === Number(params.id));

      if (index === -1) {
        throw new Error("Todo not found");
      }

      todos.splice(index, 1);
      store.todos.value = [...todos];

      // Track todo count for verification
      removeTodo();

      return { success: true };
    },
    {
      params: t.Object({
        id: t.String(),
      }),
    }
  );

export type App = typeof app;
