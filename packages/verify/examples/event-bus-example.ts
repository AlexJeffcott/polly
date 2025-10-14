// ═══════════════════════════════════════════════════════════════
// Event Bus Example Application
// ═══════════════════════════════════════════════════════════════
//
// This example demonstrates using the EventBusAdapter to verify
// an event-driven application using a simple EventBus implementation.

import { requires, ensures } from "../src/core/primitives"

// Simple EventBus implementation (Bun-native, no Node.js imports needed)
class EventBus extends EventTarget {
  private listeners = new Map<string, Set<Function>>()

  on(event: string, handler: Function): void {
    if (!this.listeners.has(event)) {
      this.listeners.set(event, new Set())
    }
    this.listeners.get(event)!.add(handler)
  }

  emit(event: string, payload?: any): void {
    const handlers = this.listeners.get(event)
    if (handlers) {
      for (const handler of handlers) {
        handler(payload)
      }
    }
  }

  off(event: string, handler: Function): void {
    const handlers = this.listeners.get(event)
    if (handlers) {
      handlers.delete(handler)
    }
  }
}

// ─────────────────────────────────────────────────────────────────
// Application State
// ─────────────────────────────────────────────────────────────────

type AppState = {
  user: {
    loggedIn: boolean
    username: string | null
    role: "admin" | "user" | "guest"
  }
  notifications: {
    count: number
    messages: string[]
  }
}

const state: AppState = {
  user: {
    loggedIn: false,
    username: null,
    role: "guest",
  },
  notifications: {
    count: 0,
    messages: [],
  },
}

// ─────────────────────────────────────────────────────────────────
// Event Bus Setup
// ─────────────────────────────────────────────────────────────────

const appBus = new EventBus()

// ─────────────────────────────────────────────────────────────────
// Event Handlers
// ─────────────────────────────────────────────────────────────────

/**
 * Handle user login event
 */
appBus.on("USER_LOGIN", (payload: { username: string; role: "admin" | "user" }) => {
  requires(state.user.loggedIn === false, "User must not already be logged in")
  requires(payload.username.length > 0, "Username must not be empty")

  state.user.loggedIn = true
  state.user.username = payload.username
  state.user.role = payload.role

  ensures(state.user.loggedIn === true, "User must be logged in after login")
  ensures(state.user.username !== null, "Username must be set after login")
})

/**
 * Handle user logout event
 */
appBus.on("USER_LOGOUT", () => {
  requires(state.user.loggedIn === true, "User must be logged in to logout")

  state.user.loggedIn = false
  state.user.username = null
  state.user.role = "guest"

  ensures(state.user.loggedIn === false, "User must be logged out")
  ensures(state.user.username === null, "Username must be cleared")
  ensures(state.user.role === "guest", "Role must be reset to guest")
})

/**
 * Handle notification event
 */
appBus.on("NOTIFICATION_ADD", (payload: { message: string }) => {
  requires(state.notifications.count < 10, "Cannot exceed 10 notifications")
  requires(payload.message.length > 0, "Message cannot be empty")

  state.notifications.count = state.notifications.count + 1
  state.notifications.messages.push(payload.message)

  ensures(state.notifications.count > 0, "Count must be incremented")
  ensures(
    state.notifications.messages.length === state.notifications.count,
    "Message count must match array length"
  )
})

/**
 * Handle notification clear event
 */
appBus.on("NOTIFICATIONS_CLEAR", () => {
  state.notifications.count = 0
  state.notifications.messages = []

  ensures(state.notifications.count === 0, "Count must be zero")
  ensures(state.notifications.messages.length === 0, "Messages must be empty")
})

/**
 * Handle admin-only action
 */
appBus.on("ADMIN_ACTION", (payload: { action: string }) => {
  requires(state.user.loggedIn === true, "User must be logged in")
  requires(state.user.role === "admin", "User must be admin")

  // Admin action logic here
  console.log(`Admin ${state.user.username} performed: ${payload.action}`)
})

// ─────────────────────────────────────────────────────────────────
// Example Usage
// ─────────────────────────────────────────────────────────────────

// Simulate user login
appBus.emit("USER_LOGIN", { username: "alice", role: "admin" })

// Add some notifications
appBus.emit("NOTIFICATION_ADD", { message: "Welcome to the app!" })
appBus.emit("NOTIFICATION_ADD", { message: "You have 3 new messages" })

// Admin action
appBus.emit("ADMIN_ACTION", { action: "delete_user" })

// Clear notifications
appBus.emit("NOTIFICATIONS_CLEAR")

// Logout
appBus.emit("USER_LOGOUT")

console.log("Event bus example completed successfully!")
console.log("Final state:", state)
