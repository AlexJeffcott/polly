import { $serverState, $syncedState } from "@fairfox/polly";
import type { PollyConfig } from "@fairfox/polly/elysia";
import { exportTLASpec } from "@fairfox/polly/elysia";
import { signal } from "@preact/signals-core";

/**
 * Generate TLA+ specification from Polly middleware config
 *
 * This extracts the Polly configuration from the server and generates
 * a formal TLA+ specification that can be verified with TLC.
 */

// Recreate the Polly config (same as in index.ts)
const pollyConfig: PollyConfig = {
  state: {
    client: {
      todos: $syncedState("todos", []),
      user: $syncedState("user", null),
    },
    server: {
      db: $serverState("db", signal({ todos: [], users: [], nextTodoId: 1 })),
    },
  },

  effects: {
    "POST /todos": {
      client: ({ result, state }) => {
        state.client.todos.value = [...state.client.todos.value, result];
      },
      broadcast: true,
    },

    "PATCH /todos/:id": {
      client: ({ result, state }) => {
        state.client.todos.value = state.client.todos.value.map((t) =>
          t.id === result.id ? result : t
        );
      },
      broadcast: true,
    },

    "DELETE /todos/:id": {
      client: ({ params, state }) => {
        state.client.todos.value = state.client.todos.value.filter(
          (t) => t.id !== Number(params.id)
        );
      },
      broadcast: true,
    },

    "POST /auth/login": {
      client: ({ result, state }) => {
        state.client.user.value = result.user;
      },
      broadcast: false,
    },

    "POST /auth/logout": {
      client: ({ state }) => {
        state.client.user.value = null;
        state.client.todos.value = [];
      },
      broadcast: false,
    },
  },

  authorization: {
    "POST /todos": ({ state }) => state.client.user.value !== null,
    "PATCH /todos/:id": ({ state }) => state.client.user.value !== null,
    "DELETE /todos/:id": ({ state }) => state.client.user.value !== null,
  },

  offline: {
    "POST /todos": {
      queue: true,
      optimistic: (body) => ({
        id: -Date.now(),
        text: body.text,
        completed: false,
      }),
    },
  },

  tlaGeneration: true,
};

async function main() {
  console.log("Generating TLA+ specification...");

  // Export to file
  const outputPath = "./specs/output/TodoApp.tla";
  await exportTLASpec("TodoApp", pollyConfig, outputPath);

  console.log(`✅ Generated: ${outputPath}`);
  console.log("\nTo verify with TLC:");
  console.log("  1. Install TLA+ Toolbox: https://lamport.azurewebsites.net/tla/toolbox.html");
  console.log(`  2. Open ${outputPath}`);
  console.log("  3. Create a model with:");
  console.log("     - Clients = {c1, c2, c3}");
  console.log("     - MaxMessages = 5");
  console.log("  4. Run TLC model checker");
  console.log("\nProperties to check:");
  console.log("  - TypeOK (type invariant)");
  console.log("  - AuthorizationEnforced (safety)");
  console.log("  - EventualConsistency (liveness)");
  console.log("  - NetworkBounded (safety)");
}

main().catch((error) => {
  throw error;
});
