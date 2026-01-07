import type { VerificationConfig } from "@fairfox/polly/verify";

/**
 * Polly Verification Configuration for Elysia Todo App
 *
 * This config generates TLA+ specifications from the Polly middleware
 * configuration and verifies distributed systems properties.
 */
export const config: VerificationConfig = {
  // Project metadata
  project: {
    name: "elysia-todo-app",
    version: "0.1.0",
  },

  // Entry point for analysis (Elysia server)
  entryPoint: "./src/index.ts",

  // Verification bounds
  bounds: {
    // Maximum concurrent requests
    maxInFlight: 2,

    // Maximum todos (matches app logic)
    maxTodos: 10,

    // Maximum clients (for broadcast testing)
    maxClients: 3,
  },

  // Properties to verify
  properties: {
    // Safety: Authorization always enforced
    authorizationEnforced: {
      type: "invariant",
      description: "Unauthenticated users cannot create/update/delete todos",
    },

    // Safety: No lost updates
    noLostUpdates: {
      type: "invariant",
      description: "All todo operations eventually reach the server",
    },

    // Liveness: Eventually consistent
    eventualConsistency: {
      type: "temporal",
      description: "All online clients eventually have the same state",
    },

    // Safety: Broadcast reaches all clients
    broadcastDelivery: {
      type: "invariant",
      description: "When a todo is created, all online clients receive it",
    },
  },

  // Verification options
  verification: {
    timeout: 120, // 2 minutes
    workers: 4,
    checkDeadlocks: true,
  },

  // Output configuration
  output: {
    directory: "./specs/output",
    generateDiagrams: true,
    verbose: true,
  },
};
