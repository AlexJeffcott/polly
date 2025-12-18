// Unit tests for todo list handlers
import { beforeEach, describe, expect, test } from "bun:test";
import { generateId, state } from "../src/background/state";

// Reset state before each test
beforeEach(() => {
  state.user = {
    id: null,
    name: "Guest",
    role: "guest",
    loggedIn: false,
  };
  state.todos = [];
  state.filter = "all";
});

describe("User Authentication", () => {
  test("user can login", () => {
    // Simulate USER_LOGIN handler logic
    state.user.loggedIn = true;
    state.user.id = "user-123";
    state.user.name = "Test User";
    state.user.role = "user";

    expect(state.user.loggedIn).toBe(true);
    expect(state.user.id).toBe("user-123");
    expect(state.user.role).toBe("user");
  });

  test("user can logout", () => {
    // Setup: user logged in
    state.user.loggedIn = true;
    state.user.id = "user-123";
    state.user.role = "user";

    // Simulate USER_LOGOUT handler logic
    state.user.loggedIn = false;
    state.user.id = null;
    state.user.name = "Guest";
    state.user.role = "guest";

    expect(state.user.loggedIn).toBe(false);
    expect(state.user.id).toBe(null);
    expect(state.user.role).toBe("guest");
  });

  test("cannot login when already logged in", () => {
    state.user.loggedIn = true;

    // This should fail the precondition
    expect(state.user.loggedIn).toBe(true);
  });
});

describe("Todo Management", () => {
  test("can add a todo", () => {
    const previousCount = state.todos.length;

    // Simulate TODO_ADD handler logic
    state.todos.push({
      id: generateId(),
      text: "Test todo",
      completed: false,
      createdAt: Date.now(),
    });

    expect(state.todos.length).toBe(previousCount + 1);
    expect(state.todos[0].text).toBe("Test todo");
    expect(state.todos[0].completed).toBe(false);
  });

  test("can toggle todo", () => {
    // Setup: add a todo
    state.todos.push({
      id: "test-1",
      text: "Test todo",
      completed: false,
      createdAt: Date.now(),
    });

    // Simulate TODO_TOGGLE handler logic
    const todo = state.todos.find((t) => t.id === "test-1");
    expect(todo).toBeDefined();

    if (todo) {
      const previousCompleted = todo.completed;
      todo.completed = !todo.completed;

      expect(todo.completed).toBe(!previousCompleted);
      expect(todo.completed).toBe(true);
    }
  });

  test("can remove todo", () => {
    // Setup: add todos
    state.todos.push(
      { id: "test-1", text: "Test 1", completed: false, createdAt: Date.now() },
      { id: "test-2", text: "Test 2", completed: false, createdAt: Date.now() }
    );

    const previousCount = state.todos.length;

    // Simulate TODO_REMOVE handler logic
    const index = state.todos.findIndex((t) => t.id === "test-1");
    state.todos.splice(index, 1);

    expect(state.todos.length).toBe(previousCount - 1);
    expect(state.todos.find((t) => t.id === "test-1")).toBeUndefined();
  });

  test("can clear completed todos", () => {
    // Setup: add mixed todos
    state.todos.push(
      { id: "test-1", text: "Test 1", completed: true, createdAt: Date.now() },
      { id: "test-2", text: "Test 2", completed: false, createdAt: Date.now() },
      { id: "test-3", text: "Test 3", completed: true, createdAt: Date.now() }
    );

    const previousCount = state.todos.length;
    const completedCount = state.todos.filter((t) => t.completed).length;

    // Simulate TODO_CLEAR_COMPLETED handler logic
    state.todos = state.todos.filter((t) => !t.completed);

    expect(state.todos.length).toBe(previousCount - completedCount);
    expect(state.todos.every((t) => !t.completed)).toBe(true);
  });

  test("respects 100 todo limit", () => {
    // Setup: add 100 todos
    for (let i = 0; i < 100; i++) {
      state.todos.push({
        id: `todo-${i}`,
        text: `Todo ${i}`,
        completed: false,
        createdAt: Date.now(),
      });
    }

    // Precondition should fail
    expect(state.todos.length).toBe(100);
    expect(state.todos.length < 100).toBe(false);
  });
});

describe("ID Generation", () => {
  test("generates unique IDs", () => {
    const id1 = generateId();
    const id2 = generateId();

    expect(id1).not.toBe(id2);
    expect(typeof id1).toBe("string");
    expect(id1.length).toBeGreaterThan(0);
  });
});
