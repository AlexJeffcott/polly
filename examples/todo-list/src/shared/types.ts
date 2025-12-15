// Shared types for todo list extension

export type Todo = {
  id: string
  text: string
  completed: boolean
  createdAt: number
}

export type User = {
  id: string | null
  name: string
  role: "guest" | "user" | "admin"
  loggedIn: boolean
}

export type AppState = {
  user: User
  todos: Todo[]
  filter: "all" | "active" | "completed"
}
