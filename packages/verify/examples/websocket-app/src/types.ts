// ═══════════════════════════════════════════════════════════════
// Types for WebSocket Chat + Todo Application
// ═══════════════════════════════════════════════════════════════
//
// This example uses Eden types for end-to-end type safety between
// client and server, and demonstrates how verification works with
// type-safe RPC messaging.

import { t, type Static } from "elysia"

// ─────────────────────────────────────────────────────────────────
// Domain Types
// ─────────────────────────────────────────────────────────────────

export const UserSchema = t.Object({
  id: t.String(),
  username: t.String(),
  online: t.Boolean(),
  joinedAt: t.Number(), // timestamp
})

export const TodoSchema = t.Object({
  id: t.String(),
  text: t.String(),
  completed: t.Boolean(),
  createdBy: t.String(), // user id
  createdAt: t.Number(), // timestamp
})

export const ChatMessageSchema = t.Object({
  id: t.String(),
  userId: t.String(),
  username: t.String(),
  text: t.String(),
  timestamp: t.Number(),
})

export type User = Static<typeof UserSchema>
export type Todo = Static<typeof TodoSchema>
export type ChatMessage = Static<typeof ChatMessageSchema>

// ─────────────────────────────────────────────────────────────────
// WebSocket Message Schema (Eden Treaty)
// ─────────────────────────────────────────────────────────────────

// Client -> Server messages
export const ClientMessageSchema = t.Union([
  // User actions
  t.Object({
    type: t.Literal("USER_JOIN"),
    payload: t.Object({
      username: t.String(),
    }),
  }),
  t.Object({
    type: t.Literal("USER_LEAVE"),
    payload: t.Object({}),
  }),

  // Chat actions
  t.Object({
    type: t.Literal("CHAT_SEND"),
    payload: t.Object({
      text: t.String(),
    }),
  }),

  // Todo actions
  t.Object({
    type: t.Literal("TODO_CREATE"),
    payload: t.Object({
      text: t.String(),
    }),
  }),
  t.Object({
    type: t.Literal("TODO_TOGGLE"),
    payload: t.Object({
      todoId: t.String(),
    }),
  }),
  t.Object({
    type: t.Literal("TODO_DELETE"),
    payload: t.Object({
      todoId: t.String(),
    }),
  }),

  // Sync actions
  t.Object({
    type: t.Literal("SYNC_REQUEST"),
    payload: t.Object({}),
  }),
])

// Server -> Client messages
export const ServerMessageSchema = t.Union([
  // Connection events
  t.Object({
    type: t.Literal("CONNECTED"),
    payload: t.Object({
      userId: t.String(),
      users: t.Array(UserSchema),
      todos: t.Array(TodoSchema),
      messages: t.Array(ChatMessageSchema),
    }),
  }),

  // User events
  t.Object({
    type: t.Literal("USER_JOINED"),
    payload: t.Object({
      user: UserSchema,
    }),
  }),
  t.Object({
    type: t.Literal("USER_LEFT"),
    payload: t.Object({
      userId: t.String(),
    }),
  }),

  // Chat events
  t.Object({
    type: t.Literal("CHAT_MESSAGE"),
    payload: t.Object({
      message: ChatMessageSchema,
    }),
  }),

  // Todo events
  t.Object({
    type: t.Literal("TODO_CREATED"),
    payload: t.Object({
      todo: TodoSchema,
    }),
  }),
  t.Object({
    type: t.Literal("TODO_UPDATED"),
    payload: t.Object({
      todo: TodoSchema,
    }),
  }),
  t.Object({
    type: t.Literal("TODO_DELETED"),
    payload: t.Object({
      todoId: t.String(),
    }),
  }),

  // Error events
  t.Object({
    type: t.Literal("ERROR"),
    payload: t.Object({
      message: t.String(),
      code: t.Optional(t.String()),
    }),
  }),
])

export type ClientMessage = Static<typeof ClientMessageSchema>
export type ServerMessage = Static<typeof ServerMessageSchema>

// ─────────────────────────────────────────────────────────────────
// Application State (for verification)
// ─────────────────────────────────────────────────────────────────

export type AppState = {
  // Connection state
  connections: {
    count: number
    maxConcurrent: number
  }

  // User state
  users: {
    online: number
    total: number
  }

  // Chat state
  chat: {
    messageCount: number
    maxMessages: number
  }

  // Todo state
  todos: {
    count: number
    completed: number
    maxTodos: number
  }

  // System state
  system: {
    initialized: boolean
    dbConnected: boolean
  }
}
