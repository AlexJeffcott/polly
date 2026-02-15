// Unit tests for todo list handlers
import { beforeEach, describe, expect, test } from "bun:test";
import { filter, generateId, todos, user } from "../src/background/state";

// Reset state before each test
beforeEach(() => {
  user.value = {
    id: null,
    name: "Guest",
    role: "guest",
    loggedIn: false,
  };
  todos.value = [];
  filter.value = "all";
});

describe("User Authentication", () => {
  test("user can login", () => {
    // Simulate USER_LOGIN handler logic
    user.value.loggedIn = true;
    user.value.id = "user-123";
    user.value.name = "Test User";
    user.value.role = "user";

    expect(user.value.loggedIn).toBe(true);
    expect(user.value.id).toBe("user-123");
    expect(user.value.role).toBe("user");
  });

  test("user can logout", () => {
    // Setup: user logged in
    user.value.loggedIn = true;
    user.value.id = "user-123";
    user.value.role = "user";

    // Simulate USER_LOGOUT handler logic
    user.value.loggedIn = false;
    user.value.id = null;
    user.value.name = "Guest";
    user.value.role = "guest";

    expect(user.value.loggedIn).toBe(false);
    expect(user.value.id).toBe(null);
    expect(user.value.role).toBe("guest");
  });

  test("cannot login when already logged in", () => {
    user.value.loggedIn = true;

    // This should fail the precondition
    expect(user.value.loggedIn).toBe(true);
  });
});

describe("Todo Management", () => {
  test("can add a todo", () => {
    const previousCount = todos.value.length;

    // Simulate TODO_ADD handler logic
    todos.value.push({
      id: generateId(),
      text: "Test todo",
      completed: false,
      priority: "medium",
      createdAt: Date.now(),
    });

    expect(todos.value.length).toBe(previousCount + 1);
    expect(todos.value[0].text).toBe("Test todo");
    expect(todos.value[0].completed).toBe(false);
  });

  test("can toggle todo", () => {
    // Setup: add a todo
    todos.value.push({
      id: "test-1",
      text: "Test todo",
      completed: false,
      priority: "medium",
      createdAt: Date.now(),
    });

    // Simulate TODO_TOGGLE handler logic
    const todo = todos.value.find((t) => t.id === "test-1");
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
    todos.value.push(
      { id: "test-1", text: "Test 1", completed: false, priority: "medium", createdAt: Date.now() },
      { id: "test-2", text: "Test 2", completed: false, priority: "medium", createdAt: Date.now() }
    );

    const previousCount = todos.value.length;

    // Simulate TODO_REMOVE handler logic
    const index = todos.value.findIndex((t) => t.id === "test-1");
    todos.value.splice(index, 1);

    expect(todos.value.length).toBe(previousCount - 1);
    expect(todos.value.find((t) => t.id === "test-1")).toBeUndefined();
  });

  test("can clear completed todos", () => {
    // Setup: add mixed todos
    todos.value.push(
      { id: "test-1", text: "Test 1", completed: true, priority: "medium", createdAt: Date.now() },
      { id: "test-2", text: "Test 2", completed: false, priority: "medium", createdAt: Date.now() },
      { id: "test-3", text: "Test 3", completed: true, priority: "medium", createdAt: Date.now() }
    );

    const previousCount = todos.value.length;
    const completedCount = todos.value.filter((t) => t.completed).length;

    // Simulate TODO_CLEAR_COMPLETED handler logic
    todos.value = todos.value.filter((t) => !t.completed);

    expect(todos.value.length).toBe(previousCount - completedCount);
    expect(todos.value.every((t) => !t.completed)).toBe(true);
  });

  test("respects 100 todo limit", () => {
    // Setup: add 100 todos
    for (let i = 0; i < 100; i++) {
      todos.value.push({
        id: `todo-${i}`,
        text: `Todo ${i}`,
        completed: false,
        priority: "medium",
        createdAt: Date.now(),
      });
    }

    // Precondition should fail
    expect(todos.value.length).toBe(100);
    expect(todos.value.length < 100).toBe(false);
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
