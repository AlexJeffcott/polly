// ═══════════════════════════════════════════════════════════════
// Bun WebSocket Server
// ═══════════════════════════════════════════════════════════════

import { AppDatabase } from "./db"
import {
  state,
  handleSystemInit,
  handleConnection,
  handleDisconnection,
  handleUserJoin,
  handleUserLeave,
  handleChatSend,
  handleTodoCreate,
  handleTodoToggle,
  handleTodoDelete,
  handleSyncRequest,
  type HandlerContext,
} from "./handlers"
import type { ClientMessage, ServerMessage } from "./types"
import type { ServerWebSocket } from "bun"

// ─────────────────────────────────────────────────────────────────
// Server State
// ─────────────────────────────────────────────────────────────────

const db = new AppDatabase(":memory:")
const connections = new Set<ServerWebSocket<{ userId?: string }>>()

// Initialize system
handleSystemInit(db)

// ─────────────────────────────────────────────────────────────────
// Broadcast Helper
// ─────────────────────────────────────────────────────────────────

function broadcast(message: ServerMessage, excludeWs?: ServerWebSocket<any>): void {
  const data = JSON.stringify(message)
  for (const ws of connections) {
    if (ws !== excludeWs && ws.readyState === 1) {
      ws.send(data)
    }
  }
}

// ─────────────────────────────────────────────────────────────────
// Message Router
// ─────────────────────────────────────────────────────────────────

function routeMessage(ctx: HandlerContext, message: ClientMessage): void {
  try {
    switch (message.type) {
      case "USER_JOIN":
        handleUserJoin(ctx, message)
        break

      case "USER_LEAVE":
        handleUserLeave(ctx, message)
        break

      case "CHAT_SEND":
        handleChatSend(ctx, message)
        break

      case "TODO_CREATE":
        handleTodoCreate(ctx, message)
        break

      case "TODO_TOGGLE":
        handleTodoToggle(ctx, message)
        break

      case "TODO_DELETE":
        handleTodoDelete(ctx, message)
        break

      case "SYNC_REQUEST":
        handleSyncRequest(ctx, message)
        break

      default:
        // @ts-expect-error - exhaustive check
        console.warn("Unknown message type:", message.type)
    }
  } catch (error) {
    console.error("Error handling message:", error)
    ctx.ws.send(JSON.stringify({
      type: "ERROR",
      payload: {
        message: error instanceof Error ? error.message : "Unknown error",
      },
    } satisfies ServerMessage))
  }
}

// ─────────────────────────────────────────────────────────────────
// WebSocket Server
// ─────────────────────────────────────────────────────────────────

const server = Bun.serve<{ userId?: string }>({
  port: 3000,
  fetch(req, server) {
    const url = new URL(req.url)

    // WebSocket upgrade
    if (url.pathname === "/ws") {
      const upgraded = server.upgrade(req, {
        data: { userId: undefined as string | undefined },
      })
      if (upgraded) return undefined
      return new Response("WebSocket upgrade failed", { status: 400 })
    }

    // Health check
    if (url.pathname === "/health") {
      return new Response(JSON.stringify({
        status: "ok",
        connections: state.connections.count,
        users: state.users.online,
        todos: state.todos.count,
        messages: state.chat.messageCount,
      }), {
        headers: { "Content-Type": "application/json" },
      })
    }

    // Stats endpoint
    if (url.pathname === "/stats") {
      return new Response(JSON.stringify(state, null, 2), {
        headers: { "Content-Type": "application/json" },
      })
    }

    return new Response("Not Found", { status: 404 })
  },

  websocket: {
    open(ws) {
      connections.add(ws)
      const ctx: HandlerContext = { ws, db, broadcast }
      handleConnection(ctx)
      console.log(`Connection opened (total: ${state.connections.count})`)
    },

    message(ws, message) {
      const ctx: HandlerContext = { ws, db, broadcast }

      try {
        const parsed = JSON.parse(message.toString()) as ClientMessage
        routeMessage(ctx, parsed)
      } catch (error) {
        console.error("Error parsing message:", error)
        ws.send(JSON.stringify({
          type: "ERROR",
          payload: {
            message: "Invalid message format",
          },
        } satisfies ServerMessage))
      }
    },

    close(ws) {
      connections.delete(ws)
      const ctx: HandlerContext = { ws, db, broadcast }
      handleDisconnection(ctx)
      console.log(`Connection closed (total: ${state.connections.count})`)
    },
  },
})

console.log(`
🚀 WebSocket Chat + Todo Server

WebSocket:  ws://localhost:${server.port}/ws
Health:     http://localhost:${server.port}/health
Stats:      http://localhost:${server.port}/stats

System initialized with:
- Users: ${state.users.total}
- Todos: ${state.todos.count}
- Messages: ${state.chat.messageCount}
`)

// Graceful shutdown
process.on("SIGINT", () => {
  console.log("\nShutting down...")
  db.close()
  server.stop()
  process.exit(0)
})
