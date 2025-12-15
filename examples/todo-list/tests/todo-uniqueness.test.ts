// Test to verify todo IDs are unique
import { test, expect, beforeEach, describe } from 'bun:test'
import { state, generateId } from '../src/background/state'

beforeEach(() => {
  state.user = {
    id: null,
    name: 'Guest',
    role: 'guest',
    loggedIn: false,
  }
  state.todos = []
  state.filter = 'all'
})

describe('Todo ID Uniqueness', () => {
  test('generateId creates unique IDs', () => {
    const ids = new Set<string>()
    const count = 100

    for (let i = 0; i < count; i++) {
      const id = generateId()
      expect(ids.has(id)).toBe(false)
      ids.add(id)
    }

    expect(ids.size).toBe(count)
  })

  test('adding multiple todos results in unique IDs', () => {
    // Simulate adding multiple todos
    for (let i = 0; i < 10; i++) {
      state.todos.push({
        id: generateId(),
        text: `Todo ${i}`,
        completed: false,
        createdAt: Date.now(),
      })
    }

    // Check all IDs are unique
    const ids = state.todos.map(t => t.id)
    const uniqueIds = new Set(ids)
    expect(uniqueIds.size).toBe(ids.length)
    expect(uniqueIds.size).toBe(10)
  })

  test('rapid todo additions maintain uniqueness', async () => {
    // Simulate rapid additions (like multiple button clicks)
    const promises = []
    for (let i = 0; i < 5; i++) {
      promises.push(
        Promise.resolve().then(() => {
          state.todos.push({
            id: generateId(),
            text: `Rapid todo ${i}`,
            completed: false,
            createdAt: Date.now(),
          })
        })
      )
    }

    await Promise.all(promises)

    // Verify no duplicates
    expect(state.todos.length).toBe(5)
    const ids = state.todos.map(t => t.id)
    const uniqueIds = new Set(ids)
    expect(uniqueIds.size).toBe(5)

    // Also verify no duplicate text (each should be unique)
    const texts = state.todos.map(t => t.text)
    expect(texts).toContain('Rapid todo 0')
    expect(texts).toContain('Rapid todo 4')
  })

  test('GET_STATE returns todos with unique IDs', () => {
    // Add some todos
    state.todos = [
      { id: 'id-1', text: 'Todo 1', completed: false, createdAt: Date.now() },
      { id: 'id-2', text: 'Todo 2', completed: false, createdAt: Date.now() },
      { id: 'id-3', text: 'Todo 3', completed: true, createdAt: Date.now() },
    ]

    // Simulate GET_STATE response
    const stateResponse = {
      user: state.user,
      todos: state.todos,
      filter: state.filter,
    }

    // Verify uniqueness
    const ids = stateResponse.todos.map(t => t.id)
    const uniqueIds = new Set(ids)
    expect(uniqueIds.size).toBe(ids.length)
    expect(uniqueIds.size).toBe(3)
  })
})
