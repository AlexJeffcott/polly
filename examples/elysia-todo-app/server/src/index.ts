import { cors } from "@elysiajs/cors";
import { $serverState, $syncedState } from "@fairfox/polly";
import { polly } from "@fairfox/polly/elysia";
import { signal } from "@preact/signals-core";
import { Elysia, t } from "elysia";

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

// Polly-enhanced Elysia app
const app = new Elysia()
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
        },
      },

      // Define client-side effects
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
            // Update specific todo in client state
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

        "POST /auth/login": {
          client: ({ result, state }) => {
            // Set logged-in user
            state.client.user.value = result.user;
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
      authorization: {
        "POST /todos": ({ state }) => state.client.user.value !== null,
        "PATCH /todos/:id": ({ state }) => state.client.user.value !== null,
        "DELETE /todos/:id": ({ state }) => state.client.user.value !== null,
      },

      // Offline behavior
      offline: {
        "POST /todos": {
          queue: true, // Queue when offline
          optimistic: (body) => ({
            id: -Date.now(), // Temporary negative ID
            text: body.text,
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
    ({ body }) => {
      const user = db.users.value.find((u) => u.username === body.username);
      if (!user) {
        throw new Error("User not found");
      }
      return { user, token: "demo-token" };
    },
    {
      body: t.Object({
        username: t.String(),
      }),
    }
  )

  .post("/auth/logout", () => {
    return { success: true };
  })

  // Todo endpoints
  .get("/todos", ({ pollyState }) => {
    return pollyState.server.db.value.todos.value;
  })

  .post(
    "/todos",
    ({ body, pollyState }) => {
      const todo: Todo = {
        id: pollyState.server.db.value.nextTodoId++,
        text: body.text,
        completed: false,
      };

      pollyState.server.db.value.todos.value = [...pollyState.server.db.value.todos.value, todo];

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
      const todos = pollyState.server.db.value.todos.value;
      const todo = todos.find((t) => t.id === Number(params.id));

      if (!todo) {
        throw new Error("Todo not found");
      }

      // Update todo
      Object.assign(todo, body);

      // Trigger reactivity
      pollyState.server.db.value.todos.value = [...todos];

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
      const todos = pollyState.server.db.value.todos.value;
      const index = todos.findIndex((t) => t.id === Number(params.id));

      if (index === -1) {
        throw new Error("Todo not found");
      }

      todos.splice(index, 1);
      pollyState.server.db.value.todos.value = [...todos];

      return { success: true };
    },
    {
      params: t.Object({
        id: t.String(),
      }),
    }
  )

  .listen(3000);

console.log(`🦊 Elysia server running at ${app.server?.hostname}:${app.server?.port}`);

export type App = typeof app;
