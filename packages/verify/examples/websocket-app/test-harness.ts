// ═══════════════════════════════════════════════════════════════
// WebSocket Test Harness - Concurrent Client Simulation
// ═══════════════════════════════════════════════════════════════
//
// Simulates multiple concurrent clients to demonstrate:
// - Race conditions in state management
// - Message ordering under load
// - Verification constraint violations
// - Broadcast consistency

import type { ClientMessage, ServerMessage } from "./src/types"

// ─────────────────────────────────────────────────────────────────
// Test Client
// ─────────────────────────────────────────────────────────────────

class TestClient {
  private ws: WebSocket | null = null
  private messageQueue: ServerMessage[] = []
  private connected = false
  public userId?: string
  public username: string

  constructor(public readonly id: number, username: string) {
    this.username = username
  }

  async connect(url: string): Promise<void> {
    return new Promise((resolve, reject) => {
      this.ws = new WebSocket(url)

      this.ws.onopen = () => {
        this.connected = true
        console.log(`[Client ${this.id}] Connected`)
        resolve()
      }

      this.ws.onmessage = (event) => {
        const message = JSON.parse(event.data) as ServerMessage
        this.messageQueue.push(message)
        this.handleMessage(message)
      }

      this.ws.onerror = (error) => {
        console.error(`[Client ${this.id}] Error:`, error)
        reject(error)
      }

      this.ws.onclose = () => {
        this.connected = false
        console.log(`[Client ${this.id}] Disconnected`)
      }
    })
  }

  private handleMessage(message: ServerMessage): void {
    switch (message.type) {
      case "CONNECTED":
        this.userId = message.payload.userId
        console.log(`[Client ${this.id}] Received userId: ${this.userId}`)
        break

      case "USER_JOINED":
        console.log(`[Client ${this.id}] User joined: ${message.payload.user.username}`)
        break

      case "CHAT_MESSAGE":
        console.log(`[Client ${this.id}] Chat: ${message.payload.message.username}: ${message.payload.message.text}`)
        break

      case "TODO_CREATED":
        console.log(`[Client ${this.id}] Todo created: ${message.payload.todo.text}`)
        break

      case "TODO_UPDATED":
        console.log(`[Client ${this.id}] Todo updated: ${message.payload.todo.id}`)
        break

      case "TODO_DELETED":
        console.log(`[Client ${this.id}] Todo deleted: ${message.payload.todoId}`)
        break

      case "ERROR":
        console.error(`[Client ${this.id}] Error: ${message.payload.message}`)
        break
    }
  }

  send(message: ClientMessage): void {
    if (!this.ws || !this.connected) {
      throw new Error("Not connected")
    }
    this.ws.send(JSON.stringify(message))
  }

  async join(): Promise<void> {
    this.send({
      type: "USER_JOIN",
      payload: { username: this.username },
    })
    // Wait for CONNECTED response
    await this.waitForMessage("CONNECTED")
  }

  sendChat(text: string): void {
    this.send({
      type: "CHAT_SEND",
      payload: { text },
    })
  }

  createTodo(text: string): void {
    this.send({
      type: "TODO_CREATE",
      payload: { text },
    })
  }

  toggleTodo(todoId: string): void {
    this.send({
      type: "TODO_TOGGLE",
      payload: { todoId },
    })
  }

  deleteTodo(todoId: string): void {
    this.send({
      type: "TODO_DELETE",
      payload: { todoId },
    })
  }

  disconnect(): void {
    if (this.ws) {
      this.ws.close()
      this.ws = null
      this.connected = false
    }
  }

  private waitForMessage(type: string, timeout = 5000): Promise<ServerMessage> {
    return new Promise((resolve, reject) => {
      const start = Date.now()
      const check = () => {
        const msg = this.messageQueue.find((m) => m.type === type)
        if (msg) {
          resolve(msg)
        } else if (Date.now() - start > timeout) {
          reject(new Error(`Timeout waiting for ${type}`))
        } else {
          setTimeout(check, 50)
        }
      }
      check()
    })
  }

  getMessages(): ServerMessage[] {
    return [...this.messageQueue]
  }
}

// ─────────────────────────────────────────────────────────────────
// Test Scenarios
// ─────────────────────────────────────────────────────────────────

async function testConcurrentJoins(url: string, count: number): Promise<void> {
  console.log(`\n🧪 Test: ${count} concurrent users joining`)

  const clients = Array.from({ length: count }, (_, i) =>
    new TestClient(i + 1, `user${i + 1}`)
  )

  // Connect all clients
  await Promise.all(clients.map((client) => client.connect(url)))

  // Join all at once (race condition test)
  await Promise.all(clients.map((client) => client.join()))

  console.log(`✅ All ${count} clients joined successfully`)

  // Cleanup
  clients.forEach((client) => client.disconnect())
}

async function testConcurrentTodoCreation(url: string, clientCount: number, todosPerClient: number): Promise<void> {
  console.log(`\n🧪 Test: ${clientCount} clients creating ${todosPerClient} todos each`)

  const clients = Array.from({ length: clientCount }, (_, i) =>
    new TestClient(i + 1, `user${i + 1}`)
  )

  // Connect and join
  await Promise.all(clients.map((client) => client.connect(url)))
  await Promise.all(clients.map((client) => client.join()))

  // Create todos concurrently
  const promises = clients.flatMap((client) =>
    Array.from({ length: todosPerClient }, (_, i) =>
      new Promise<void>((resolve) => {
        client.createTodo(`Todo ${i + 1} from ${client.username}`)
        setTimeout(resolve, 10) // Small delay between todos
      })
    )
  )

  await Promise.all(promises)

  console.log(`✅ Created ${clientCount * todosPerClient} todos concurrently`)

  // Cleanup
  clients.forEach((client) => client.disconnect())
}

async function testChatFlood(url: string, clientCount: number, messagesPerClient: number): Promise<void> {
  console.log(`\n🧪 Test: ${clientCount} clients sending ${messagesPerClient} messages each`)

  const clients = Array.from({ length: clientCount }, (_, i) =>
    new TestClient(i + 1, `user${i + 1}`)
  )

  // Connect and join
  await Promise.all(clients.map((client) => client.connect(url)))
  await Promise.all(clients.map((client) => client.join()))

  // Send messages concurrently
  const promises = clients.flatMap((client) =>
    Array.from({ length: messagesPerClient }, (_, i) =>
      new Promise<void>((resolve) => {
        client.sendChat(`Message ${i + 1} from ${client.username}`)
        setTimeout(resolve, 5) // Very small delay
      })
    )
  )

  await Promise.all(promises)

  console.log(`✅ Sent ${clientCount * messagesPerClient} messages concurrently`)

  // Cleanup
  clients.forEach((client) => client.disconnect())
}

async function testMaxConnectionLimit(url: string): Promise<void> {
  console.log(`\n🧪 Test: Exceeding max connection limit`)

  const MAX_CONNECTIONS = 100 // From handlers.ts state.connections.maxConcurrent

  // Try to create MORE than the max
  const clients = Array.from({ length: MAX_CONNECTIONS + 5 }, (_, i) =>
    new TestClient(i + 1, `user${i + 1}`)
  )

  try {
    // Connect all clients
    await Promise.all(clients.map((client) => client.connect(url)))

    // Try to join all (should fail for extras)
    const results = await Promise.allSettled(
      clients.map((client) => client.join())
    )

    const succeeded = results.filter((r) => r.status === "fulfilled").length
    const failed = results.filter((r) => r.status === "rejected").length

    console.log(`✅ ${succeeded} connections succeeded, ${failed} failed (expected)`)

    if (succeeded > MAX_CONNECTIONS) {
      console.error(`❌ Max connection limit violated! Expected <= ${MAX_CONNECTIONS}, got ${succeeded}`)
    }
  } finally {
    // Cleanup
    clients.forEach((client) => client.disconnect())
  }
}

async function testTodoLimits(url: string): Promise<void> {
  console.log(`\n🧪 Test: Exceeding max todo limit`)

  const MAX_TODOS = 50 // From handlers.ts state.todos.maxTodos

  const client = new TestClient(1, "testuser")
  await client.connect(url)
  await client.join()

  // Try to create MORE than the max
  let successCount = 0
  let errorCount = 0

  for (let i = 0; i < MAX_TODOS + 10; i++) {
    try {
      client.createTodo(`Todo ${i + 1}`)
      successCount++
      await new Promise((resolve) => setTimeout(resolve, 10))
    } catch (error) {
      errorCount++
    }
  }

  console.log(`✅ Created ${successCount} todos, ${errorCount} rejected`)

  if (successCount > MAX_TODOS) {
    console.error(`❌ Max todo limit violated! Expected <= ${MAX_TODOS}, got ${successCount}`)
  }

  client.disconnect()
}

async function testRaceCondition(url: string): Promise<void> {
  console.log(`\n🧪 Test: Race condition - multiple clients toggling same todo`)

  const clients = Array.from({ length: 5 }, (_, i) =>
    new TestClient(i + 1, `user${i + 1}`)
  )

  // Connect and join
  await Promise.all(clients.map((client) => client.connect(url)))
  await Promise.all(clients.map((client) => client.join()))

  // First client creates a todo
  clients[0].createTodo("Shared todo")
  await new Promise((resolve) => setTimeout(resolve, 100))

  // Get the todo ID from the first client's messages
  const messages = clients[0].getMessages()
  const todoCreated = messages.find((m) => m.type === "TODO_CREATED") as Extract<
    ServerMessage,
    { type: "TODO_CREATED" }
  >

  if (!todoCreated) {
    console.error("❌ Could not create todo")
    return
  }

  const todoId = todoCreated.payload.todo.id

  // All clients try to toggle it simultaneously (race condition!)
  console.log(`All clients toggling todo ${todoId} simultaneously...`)
  await Promise.all(
    clients.map((client) => {
      client.toggleTodo(todoId)
      return new Promise((resolve) => setTimeout(resolve, 10))
    })
  )

  await new Promise((resolve) => setTimeout(resolve, 500))

  console.log(`✅ Race condition test completed (check server logs for verification)`)

  // Cleanup
  clients.forEach((client) => client.disconnect())
}

// ─────────────────────────────────────────────────────────────────
// Main Test Runner
// ─────────────────────────────────────────────────────────────────

async function runTests(): Promise<void> {
  const url = "ws://localhost:3000/ws"

  console.log("═══════════════════════════════════════════════════════════════")
  console.log("WebSocket Verification Test Harness")
  console.log("═══════════════════════════════════════════════════════════════")
  console.log(`Target: ${url}`)
  console.log("")

  try {
    // Basic concurrent joins
    await testConcurrentJoins(url, 5)
    await new Promise((resolve) => setTimeout(resolve, 500))

    // Concurrent todo creation
    await testConcurrentTodoCreation(url, 3, 5)
    await new Promise((resolve) => setTimeout(resolve, 500))

    // Chat flood
    await testChatFlood(url, 3, 10)
    await new Promise((resolve) => setTimeout(resolve, 500))

    // Race condition
    await testRaceCondition(url)
    await new Promise((resolve) => setTimeout(resolve, 500))

    // Limit tests (these might fail verification!)
    await testMaxConnectionLimit(url)
    await new Promise((resolve) => setTimeout(resolve, 500))

    await testTodoLimits(url)

    console.log("\n═══════════════════════════════════════════════════════════════")
    console.log("✅ All tests completed!")
    console.log("═══════════════════════════════════════════════════════════════")
  } catch (error) {
    console.error("\n❌ Test suite failed:", error)
    process.exit(1)
  }
}

// ─────────────────────────────────────────────────────────────────
// CLI
// ─────────────────────────────────────────────────────────────────

if (import.meta.main) {
  runTests()
    .then(() => process.exit(0))
    .catch((error) => {
      console.error("Fatal error:", error)
      process.exit(1)
    })
}
