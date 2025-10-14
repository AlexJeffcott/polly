// ═══════════════════════════════════════════════════════════════
// WebSocket Message Handlers with Verification
// ═══════════════════════════════════════════════════════════════

import { requires, ensures } from "../../../src/core/primitives"
import type { AppDatabase } from "./db"
import type { ClientMessage, ServerMessage, AppState, User, Todo, ChatMessage } from "./types"
import type { ServerWebSocket } from "bun"

// ─────────────────────────────────────────────────────────────────
// Application State (tracked for verification)
// ─────────────────────────────────────────────────────────────────

export const state: AppState = {
  connections: {
    count: 0,
    maxConcurrent: 100,
  },
  users: {
    online: 0,
    total: 0,
  },
  chat: {
    messageCount: 0,
    maxMessages: 100,
  },
  todos: {
    count: 0,
    completed: 0,
    maxTodos: 50,
  },
  system: {
    initialized: false,
    dbConnected: false,
  },
}

// ─────────────────────────────────────────────────────────────────
// Handler Context
// ─────────────────────────────────────────────────────────────────

export interface HandlerContext {
  ws: ServerWebSocket<{ userId?: string }>
  db: AppDatabase
  broadcast: (message: ServerMessage, excludeWs?: ServerWebSocket<any>) => void
}

// ─────────────────────────────────────────────────────────────────
// System Handlers
// ─────────────────────────────────────────────────────────────────

export function handleSystemInit(db: AppDatabase): void {
  requires(state.system.initialized === false, "System must not be initialized")
  requires(state.system.dbConnected === false, "DB must not be connected")

  state.system.initialized = true
  state.system.dbConnected = true

  // Sync state from DB
  state.todos.count = db.getTodoCount()
  state.todos.completed = db.getCompletedCount()
  state.chat.messageCount = db.getMessageCount()
  state.users.total = db.getAllUsers().length
  state.users.online = db.getOnlineUsers().length

  ensures(state.system.initialized === true, "System must be initialized")
  ensures(state.system.dbConnected === true, "DB must be connected")
}

export function handleConnection(ctx: HandlerContext): void {
  requires(state.system.initialized === true, "System must be initialized")
  requires(state.connections.count < state.connections.maxConcurrent, "Too many connections")

  state.connections.count += 1

  ensures(state.connections.count > 0, "Connection count must increase")
  ensures(state.connections.count <= state.connections.maxConcurrent, "Must not exceed max connections")
}

export function handleDisconnection(ctx: HandlerContext): void {
  requires(state.connections.count > 0, "Must have active connections")

  const userId = ctx.ws.data.userId
  if (userId) {
    // Mark user as offline
    ctx.db.setUserOnline(userId, false)
    state.users.online -= 1

    // Broadcast user left
    ctx.broadcast({
      type: "USER_LEFT",
      payload: { userId },
    })
  }

  state.connections.count -= 1

  ensures(state.connections.count >= 0, "Connection count cannot be negative")
  ensures(state.users.online >= 0, "Online users cannot be negative")
}

// ─────────────────────────────────────────────────────────────────
// User Handlers
// ─────────────────────────────────────────────────────────────────

export function handleUserJoin(ctx: HandlerContext, message: Extract<ClientMessage, { type: "USER_JOIN" }>): void {
  requires(state.system.initialized === true, "System must be initialized")
  requires(message.payload.username.length > 0, "Username cannot be empty")
  requires(message.payload.username.length <= 20, "Username too long")

  // Check if username is already taken
  const existing = ctx.db.getUserByUsername(message.payload.username)
  if (existing) {
    ctx.ws.send(JSON.stringify({
      type: "ERROR",
      payload: {
        message: "Username already taken",
        code: "USERNAME_TAKEN",
      },
    } satisfies ServerMessage))
    return
  }

  // Create user
  const user: User = {
    id: crypto.randomUUID(),
    username: message.payload.username,
    online: true,
    joinedAt: Date.now(),
  }

  ctx.db.createUser(user)
  ctx.ws.data.userId = user.id

  state.users.online += 1
  state.users.total += 1

  // Send initial state to joining user
  ctx.ws.send(JSON.stringify({
    type: "CONNECTED",
    payload: {
      userId: user.id,
      users: ctx.db.getOnlineUsers(),
      todos: ctx.db.getAllTodos(),
      messages: ctx.db.getRecentMessages(50),
    },
  } satisfies ServerMessage))

  // Broadcast to others
  ctx.broadcast({
    type: "USER_JOINED",
    payload: { user },
  }, ctx.ws)

  ensures(state.users.online > 0, "Must have online users")
  ensures(state.users.total >= state.users.online, "Total users must be >= online users")
}

export function handleUserLeave(ctx: HandlerContext, message: Extract<ClientMessage, { type: "USER_LEAVE" }>): void {
  requires(ctx.ws.data.userId !== undefined, "Must have user ID")
  requires(state.users.online > 0, "Must have online users")

  const userId = ctx.ws.data.userId!
  ctx.db.setUserOnline(userId, false)
  state.users.online -= 1

  ctx.broadcast({
    type: "USER_LEFT",
    payload: { userId },
  })

  ensures(state.users.online >= 0, "Online users cannot be negative")
}

// ─────────────────────────────────────────────────────────────────
// Chat Handlers
// ─────────────────────────────────────────────────────────────────

export function handleChatSend(ctx: HandlerContext, message: Extract<ClientMessage, { type: "CHAT_SEND" }>): void {
  requires(ctx.ws.data.userId !== undefined, "Must be logged in")
  requires(message.payload.text.length > 0, "Message cannot be empty")
  requires(message.payload.text.length <= 500, "Message too long")
  requires(state.chat.messageCount < state.chat.maxMessages, "Chat history full")

  const userId = ctx.ws.data.userId!
  const user = ctx.db.getUser(userId)
  if (!user) {
    ctx.ws.send(JSON.stringify({
      type: "ERROR",
      payload: { message: "User not found" },
    } satisfies ServerMessage))
    return
  }

  const chatMessage: ChatMessage = {
    id: crypto.randomUUID(),
    userId: user.id,
    username: user.username,
    text: message.payload.text,
    timestamp: Date.now(),
  }

  ctx.db.createMessage(chatMessage)
  state.chat.messageCount += 1

  // Clean up old messages if needed
  if (state.chat.messageCount > state.chat.maxMessages) {
    ctx.db.deleteOldMessages(state.chat.maxMessages)
    state.chat.messageCount = state.chat.maxMessages
  }

  // Broadcast to all
  ctx.broadcast({
    type: "CHAT_MESSAGE",
    payload: { message: chatMessage },
  })

  ensures(state.chat.messageCount <= state.chat.maxMessages, "Must not exceed max messages")
}

// ─────────────────────────────────────────────────────────────────
// Todo Handlers
// ─────────────────────────────────────────────────────────────────

export function handleTodoCreate(ctx: HandlerContext, message: Extract<ClientMessage, { type: "TODO_CREATE" }>): void {
  requires(ctx.ws.data.userId !== undefined, "Must be logged in")
  requires(message.payload.text.length > 0, "Todo text cannot be empty")
  requires(message.payload.text.length <= 200, "Todo text too long")
  requires(state.todos.count < state.todos.maxTodos, "Too many todos")

  const userId = ctx.ws.data.userId!

  const todo: Todo = {
    id: crypto.randomUUID(),
    text: message.payload.text,
    completed: false,
    createdBy: userId,
    createdAt: Date.now(),
  }

  ctx.db.createTodo(todo)
  state.todos.count += 1

  // Broadcast to all
  ctx.broadcast({
    type: "TODO_CREATED",
    payload: { todo },
  })

  ensures(state.todos.count > 0, "Must have todos")
  ensures(state.todos.count <= state.todos.maxTodos, "Must not exceed max todos")
}

export function handleTodoToggle(ctx: HandlerContext, message: Extract<ClientMessage, { type: "TODO_TOGGLE" }>): void {
  requires(ctx.ws.data.userId !== undefined, "Must be logged in")
  requires(message.payload.todoId.length > 0, "Todo ID required")

  const todo = ctx.db.getTodo(message.payload.todoId)
  if (!todo) {
    ctx.ws.send(JSON.stringify({
      type: "ERROR",
      payload: { message: "Todo not found" },
    } satisfies ServerMessage))
    return
  }

  const wasCompleted = todo.completed
  const newCompleted = !todo.completed

  ctx.db.updateTodo(todo.id, { completed: newCompleted })

  if (wasCompleted && !newCompleted) {
    state.todos.completed -= 1
  } else if (!wasCompleted && newCompleted) {
    state.todos.completed += 1
  }

  const updatedTodo = ctx.db.getTodo(todo.id)!

  // Broadcast to all
  ctx.broadcast({
    type: "TODO_UPDATED",
    payload: { todo: updatedTodo },
  })

  ensures(state.todos.completed >= 0, "Completed count cannot be negative")
  ensures(state.todos.completed <= state.todos.count, "Completed cannot exceed total")
}

export function handleTodoDelete(ctx: HandlerContext, message: Extract<ClientMessage, { type: "TODO_DELETE" }>): void {
  requires(ctx.ws.data.userId !== undefined, "Must be logged in")
  requires(message.payload.todoId.length > 0, "Todo ID required")
  requires(state.todos.count > 0, "Must have todos to delete")

  const todo = ctx.db.getTodo(message.payload.todoId)
  if (!todo) {
    ctx.ws.send(JSON.stringify({
      type: "ERROR",
      payload: { message: "Todo not found" },
    } satisfies ServerMessage))
    return
  }

  if (todo.completed) {
    state.todos.completed -= 1
  }

  ctx.db.deleteTodo(todo.id)
  state.todos.count -= 1

  // Broadcast to all
  ctx.broadcast({
    type: "TODO_DELETED",
    payload: { todoId: todo.id },
  })

  ensures(state.todos.count >= 0, "Todo count cannot be negative")
  ensures(state.todos.completed >= 0, "Completed count cannot be negative")
  ensures(state.todos.completed <= state.todos.count, "Completed cannot exceed total")
}

// ─────────────────────────────────────────────────────────────────
// Sync Handler
// ─────────────────────────────────────────────────────────────────

export function handleSyncRequest(ctx: HandlerContext, message: Extract<ClientMessage, { type: "SYNC_REQUEST" }>): void {
  requires(ctx.ws.data.userId !== undefined, "Must be logged in")

  ctx.ws.send(JSON.stringify({
    type: "CONNECTED",
    payload: {
      userId: ctx.ws.data.userId!,
      users: ctx.db.getOnlineUsers(),
      todos: ctx.db.getAllTodos(),
      messages: ctx.db.getRecentMessages(50),
    },
  } satisfies ServerMessage))
}
