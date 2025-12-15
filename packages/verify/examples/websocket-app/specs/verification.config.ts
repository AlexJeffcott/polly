// ═══════════════════════════════════════════════════════════════
// Verification Configuration for WebSocket Chat + Todo App
// ═══════════════════════════════════════════════════════════════

import { defineVerification } from "../../../src/index"

export default defineVerification({
  messages: {
    maxInFlight: 2,  // Start small for fast verification
    maxClients: 2,    // 2 clients sufficient to test multi-client scenarios
    maxMessagesPerClient: 2,
  },

  state: {
    // Connection bounds
    "connections.count": { min: 0, max: 100 },
    "connections.maxConcurrent": { min: 100, max: 100 }, // Constant value

    // User bounds
    "users.online": { min: 0, max: 100 },
    "users.total": { min: 0, max: 1000 },

    // Chat bounds
    "chat.messageCount": { min: 0, max: 100 },
    "chat.maxMessages": { min: 100, max: 100 }, // Constant value

    // Todo bounds
    "todos.count": { min: 0, max: 50 },
    "todos.completed": { min: 0, max: 50 },
    "todos.maxTodos": { min: 50, max: 50 }, // Constant value

    // System state (booleans - use enum with two values)
    "system.initialized": { type: "enum", values: ["false", "true"] },
    "system.dbConnected": { type: "enum", values: ["false", "true"] },
  },

  onBuild: "warn",
  onRelease: "error",

  // Custom invariants to verify
  invariants: [
    {
      name: "ConnectionsWithinLimit",
      expression: "state.connections.count <= state.connections.maxConcurrent",
      description: "Connection count must not exceed maximum",
    },
    {
      name: "OnlineUsersLessOrEqualToConnections",
      expression: "state.users.online <= state.connections.count",
      description: "Online users cannot exceed active connections",
    },
    {
      name: "TotalUsersGreaterOrEqualToOnline",
      expression: "state.users.total >= state.users.online",
      description: "Total registered users must be >= online users",
    },
    {
      name: "ChatWithinLimit",
      expression: "state.chat.messageCount <= state.chat.maxMessages",
      description: "Chat message count must not exceed maximum",
    },
    {
      name: "TodosWithinLimit",
      expression: "state.todos.count <= state.todos.maxTodos",
      description: "Todo count must not exceed maximum",
    },
    {
      name: "CompletedLessOrEqualToTotal",
      expression: "state.todos.completed <= state.todos.count",
      description: "Completed todos cannot exceed total todos",
    },
    {
      name: "NonNegativeCounts",
      expression:
        "state.connections.count >= 0 && state.users.online >= 0 && state.users.total >= 0 && state.todos.count >= 0 && state.todos.completed >= 0 && state.chat.messageCount >= 0",
      description: "All counts must remain non-negative",
    },
    {
      name: "InitializedBeforeUse",
      expression: "state.connections.count > 0 => state.system.initialized",
      description: "System must be initialized before accepting connections",
    },
    {
      name: "DatabaseConnectedWhenInitialized",
      expression: "state.system.initialized => state.system.dbConnected",
      description: "Database must be connected when system is initialized",
    },
  ],
})
