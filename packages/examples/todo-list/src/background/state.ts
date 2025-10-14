// Application state management
import type { AppState } from '../shared/types'

export const state: AppState = {
  user: {
    id: null,
    name: 'Guest',
    role: 'guest',
    loggedIn: false,
  },
  todos: [],
  filter: 'all',
}

// Helper to generate IDs
export function generateId(): string {
  return `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`
}
