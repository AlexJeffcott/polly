// Example state type for testing verification system

export type Todo = {
  id: string
  text: string
  completed: boolean
  createdAt: number
}

export type User = {
  id: string | null
  username: string | null
  role: "admin" | "user" | "guest"
  loggedIn: boolean
}

export type AppState = {
  // User state
  user: User

  // Todo list
  todos: Todo[]

  // Counters and flags
  todoCount: number
  initialized: boolean
  syncing: boolean

  // Settings
  settings: {
    theme: "light" | "dark"
    notifications: boolean
    autoSync: boolean
  }

  // Cache
  cache: Map<string, { data: any, timestamp: number }>
}
