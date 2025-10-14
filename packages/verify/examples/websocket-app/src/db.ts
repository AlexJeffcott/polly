// ═══════════════════════════════════════════════════════════════
// SQLite Database Setup
// ═══════════════════════════════════════════════════════════════

import { Database } from "bun:sqlite"
import type { User, Todo, ChatMessage } from "./types"

export class AppDatabase {
  private db: Database

  constructor(path: string = ":memory:") {
    this.db = new Database(path)
    this.initialize()
  }

  private initialize() {
    // Users table
    this.db.run(`
      CREATE TABLE IF NOT EXISTS users (
        id TEXT PRIMARY KEY,
        username TEXT NOT NULL UNIQUE,
        online INTEGER NOT NULL DEFAULT 1,
        joinedAt INTEGER NOT NULL
      )
    `)

    // Todos table
    this.db.run(`
      CREATE TABLE IF NOT EXISTS todos (
        id TEXT PRIMARY KEY,
        text TEXT NOT NULL,
        completed INTEGER NOT NULL DEFAULT 0,
        createdBy TEXT NOT NULL,
        createdAt INTEGER NOT NULL,
        FOREIGN KEY (createdBy) REFERENCES users(id)
      )
    `)

    // Chat messages table
    this.db.run(`
      CREATE TABLE IF NOT EXISTS chat_messages (
        id TEXT PRIMARY KEY,
        userId TEXT NOT NULL,
        username TEXT NOT NULL,
        text TEXT NOT NULL,
        timestamp INTEGER NOT NULL,
        FOREIGN KEY (userId) REFERENCES users(id)
      )
    `)

    // Create indexes
    this.db.run("CREATE INDEX IF NOT EXISTS idx_users_online ON users(online)")
    this.db.run("CREATE INDEX IF NOT EXISTS idx_todos_completed ON todos(completed)")
    this.db.run("CREATE INDEX IF NOT EXISTS idx_chat_timestamp ON chat_messages(timestamp)")
  }

  // ─────────────────────────────────────────────────────────────────
  // User Operations
  // ─────────────────────────────────────────────────────────────────

  createUser(user: User): void {
    this.db.run(
      "INSERT INTO users (id, username, online, joinedAt) VALUES (?, ?, ?, ?)",
      [user.id, user.username, user.online ? 1 : 0, user.joinedAt]
    )
  }

  getUser(id: string): User | null {
    const row = this.db.query("SELECT * FROM users WHERE id = ?").get(id) as any
    if (!row) return null
    return {
      id: row.id,
      username: row.username,
      online: Boolean(row.online),
      joinedAt: row.joinedAt,
    }
  }

  getUserByUsername(username: string): User | null {
    const row = this.db.query("SELECT * FROM users WHERE username = ?").get(username) as any
    if (!row) return null
    return {
      id: row.id,
      username: row.username,
      online: Boolean(row.online),
      joinedAt: row.joinedAt,
    }
  }

  getAllUsers(): User[] {
    const rows = this.db.query("SELECT * FROM users").all() as any[]
    return rows.map((row) => ({
      id: row.id,
      username: row.username,
      online: Boolean(row.online),
      joinedAt: row.joinedAt,
    }))
  }

  getOnlineUsers(): User[] {
    const rows = this.db.query("SELECT * FROM users WHERE online = 1").all() as any[]
    return rows.map((row) => ({
      id: row.id,
      username: row.username,
      online: Boolean(row.online),
      joinedAt: row.joinedAt,
    }))
  }

  setUserOnline(id: string, online: boolean): void {
    this.db.run("UPDATE users SET online = ? WHERE id = ?", [online ? 1 : 0, id])
  }

  // ─────────────────────────────────────────────────────────────────
  // Todo Operations
  // ─────────────────────────────────────────────────────────────────

  createTodo(todo: Todo): void {
    this.db.run(
      "INSERT INTO todos (id, text, completed, createdBy, createdAt) VALUES (?, ?, ?, ?, ?)",
      [todo.id, todo.text, todo.completed ? 1 : 0, todo.createdBy, todo.createdAt]
    )
  }

  getTodo(id: string): Todo | null {
    const row = this.db.query("SELECT * FROM todos WHERE id = ?").get(id) as any
    if (!row) return null
    return {
      id: row.id,
      text: row.text,
      completed: Boolean(row.completed),
      createdBy: row.createdBy,
      createdAt: row.createdAt,
    }
  }

  getAllTodos(): Todo[] {
    const rows = this.db.query("SELECT * FROM todos ORDER BY createdAt DESC").all() as any[]
    return rows.map((row) => ({
      id: row.id,
      text: row.text,
      completed: Boolean(row.completed),
      createdBy: row.createdBy,
      createdAt: row.createdAt,
    }))
  }

  updateTodo(id: string, updates: Partial<Todo>): void {
    const fields: string[] = []
    const values: any[] = []

    if (updates.text !== undefined) {
      fields.push("text = ?")
      values.push(updates.text)
    }
    if (updates.completed !== undefined) {
      fields.push("completed = ?")
      values.push(updates.completed ? 1 : 0)
    }

    if (fields.length === 0) return

    values.push(id)
    this.db.run(`UPDATE todos SET ${fields.join(", ")} WHERE id = ?`, values)
  }

  deleteTodo(id: string): void {
    this.db.run("DELETE FROM todos WHERE id = ?", [id])
  }

  getTodoCount(): number {
    const result = this.db.query("SELECT COUNT(*) as count FROM todos").get() as any
    return result.count
  }

  getCompletedCount(): number {
    const result = this.db.query("SELECT COUNT(*) as count FROM todos WHERE completed = 1").get() as any
    return result.count
  }

  // ─────────────────────────────────────────────────────────────────
  // Chat Operations
  // ─────────────────────────────────────────────────────────────────

  createMessage(message: ChatMessage): void {
    this.db.run(
      "INSERT INTO chat_messages (id, userId, username, text, timestamp) VALUES (?, ?, ?, ?, ?)",
      [message.id, message.userId, message.username, message.text, message.timestamp]
    )
  }

  getRecentMessages(limit: number = 50): ChatMessage[] {
    const rows = this.db
      .query("SELECT * FROM chat_messages ORDER BY timestamp DESC LIMIT ?")
      .all(limit) as any[]
    return rows.reverse().map((row) => ({
      id: row.id,
      userId: row.userId,
      username: row.username,
      text: row.text,
      timestamp: row.timestamp,
    }))
  }

  getMessageCount(): number {
    const result = this.db.query("SELECT COUNT(*) as count FROM chat_messages").get() as any
    return result.count
  }

  deleteOldMessages(keepCount: number = 100): void {
    this.db.run(`
      DELETE FROM chat_messages
      WHERE id NOT IN (
        SELECT id FROM chat_messages
        ORDER BY timestamp DESC
        LIMIT ?
      )
    `, [keepCount])
  }

  // ─────────────────────────────────────────────────────────────────
  // Utility
  // ─────────────────────────────────────────────────────────────────

  close(): void {
    this.db.close()
  }

  clear(): void {
    this.db.run("DELETE FROM chat_messages")
    this.db.run("DELETE FROM todos")
    this.db.run("DELETE FROM users")
  }
}
