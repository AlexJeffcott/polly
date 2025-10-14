// Message handlers with verification primitives
import { createBackground } from '@fairfox/web-ext/background'
import { requires, ensures } from '@fairfox/web-ext-verify'
import { state, generateId } from './state'
import type { Todo } from '../shared/types'
import type { TodoMessages } from '../shared/messages'

// Initialize background script with MessageRouter
// IMPORTANT: Always use createBackground() in background scripts, NOT getMessageBus('background')
// This ensures proper message routing and prevents double-execution bugs.
// See: docs/BACKGROUND_SETUP.md for details
const bus = createBackground<TodoMessages>()

// ============================================================================
// User Authentication
// ============================================================================

bus.on('USER_LOGIN', (payload: { userId: string; name: string; role: 'user' | 'admin' }) => {
  // Preconditions
  requires(state.user.loggedIn === false, 'User must not be logged in')
  requires(payload.userId !== null && payload.userId.length > 0, 'User ID must be provided')
  requires(payload.name.length > 0, 'User name must be provided')

  // State changes
  state.user.loggedIn = true
  state.user.id = payload.userId
  state.user.name = payload.name
  state.user.role = payload.role

  // Postconditions
  ensures(state.user.loggedIn === true, 'User must be logged in')
  ensures(state.user.id === payload.userId, 'User ID must match payload')
  ensures(state.user.role === payload.role, 'User role must match payload')

  return { success: true, user: state.user }
})

bus.on('USER_LOGOUT', () => {
  // Precondition
  requires(state.user.loggedIn === true, 'User must be logged in to logout')

  // State changes
  state.user.loggedIn = false
  state.user.id = null
  state.user.name = 'Guest'
  state.user.role = 'guest'

  // Postconditions
  ensures(state.user.loggedIn === false, 'User must be logged out')
  ensures(state.user.role === 'guest', 'User must have guest role')
  ensures(state.user.id === null, 'User ID must be null')

  return { success: true }
})

// ============================================================================
// Todo Management
// ============================================================================

bus.on('TODO_ADD', (payload: { text: string }) => {
  // Preconditions
  requires(state.todos.length < 100, 'Cannot exceed 100 todos')
  requires(payload.text.length > 0, 'Todo text cannot be empty')
  requires(payload.text.length <= 500, 'Todo text too long')

  const previousCount = state.todos.length

  // State change
  const newTodo: Todo = {
    id: generateId(),
    text: payload.text,
    completed: false,
    createdAt: Date.now(),
  }
  state.todos.push(newTodo)

  // Postconditions
  ensures(state.todos.length === previousCount + 1, 'Todo count must increase by 1')
  ensures(state.todos.length > 0, 'Todo count must be positive')
  ensures(state.todos.length <= 100, 'Todo count must not exceed 100')

  // Check for duplicate IDs
  const ids = state.todos.map(t => t.id)
  const uniqueIds = new Set(ids)
  ensures(ids.length === uniqueIds.size, 'All todo IDs must be unique')

  return { success: true, todo: newTodo }
})

bus.on('TODO_TOGGLE', (payload: { id: string }) => {
  // Precondition
  const todo = state.todos.find(t => t.id === payload.id)
  requires(todo !== undefined, 'Todo must exist')

  if (todo) {
    const previousCompleted = todo.completed

    // State change
    todo.completed = !todo.completed

    // Postcondition
    ensures(todo.completed !== previousCompleted, 'Todo completed state must toggle')

    return { success: true, todo }
  }

  return { success: false, error: 'Todo not found' }
})

bus.on('TODO_REMOVE', (payload: { id: string }) => {
  // Precondition
  const index = state.todos.findIndex(t => t.id === payload.id)
  requires(index >= 0, 'Todo must exist')

  const previousCount = state.todos.length

  // State change
  state.todos.splice(index, 1)

  // Postconditions
  ensures(state.todos.length === previousCount - 1, 'Todo count must decrease by 1')
  ensures(state.todos.findIndex(t => t.id === payload.id) === -1, 'Todo must be removed')

  return { success: true }
})

bus.on('TODO_CLEAR_COMPLETED', () => {
  const previousCount = state.todos.length
  const completedCount = state.todos.filter(t => t.completed).length

  // State change
  state.todos = state.todos.filter(t => !t.completed)

  // Postconditions
  ensures(state.todos.length === previousCount - completedCount, 'Removed count must match completed count')
  ensures(state.todos.every(t => !t.completed), 'All remaining todos must be incomplete')

  return { success: true, removed: completedCount }
})

// ============================================================================
// Queries
// ============================================================================

bus.on('GET_STATE', () => {
  // Verification: ensure all todo IDs are unique
  const ids = state.todos.map(t => t.id)
  const uniqueIds = new Set(ids)
  ensures(ids.length === uniqueIds.size, 'All todo IDs must be unique in GET_STATE')

  // Return a deep copy to prevent reference sharing issues
  return {
    user: { ...state.user },
    todos: state.todos.map(t => ({ ...t })),
    filter: state.filter,
  }
})

bus.on('GET_TODOS', (payload?: { filter?: 'all' | 'active' | 'completed' }) => {
  const filter = payload?.filter || 'all'

  let filteredTodos = state.todos
  if (filter === 'active') {
    filteredTodos = state.todos.filter(t => !t.completed)
  } else if (filter === 'completed') {
    filteredTodos = state.todos.filter(t => t.completed)
  }

  return { todos: filteredTodos }
})

console.log('Todo list background script loaded!')
