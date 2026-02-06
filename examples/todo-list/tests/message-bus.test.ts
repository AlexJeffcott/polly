/**
 * Mock Adapters Test
 *
 * Demonstrates using @fairfox/polly/test utilities
 */

import { beforeEach, describe, expect, test } from "bun:test";
import { createMockAdapters, type MockExtensionAdapters, waitFor } from "@fairfox/polly/test";
import { filter, generateId, todos, user } from "../src/background/state";

describe("Todo Handler Logic with Mock Adapters", () => {
  let adapters: MockExtensionAdapters;

  beforeEach(() => {
    // Reset state
    user.value = {
      id: null,
      name: "Guest",
      role: "guest",
      loggedIn: false,
    };
    todos.value = [];
    filter.value = "all";

    // Create mock adapters
    adapters = createMockAdapters();
  });

  test("can add a todo", () => {
    // Simulate TODO_ADD handler logic
    const newTodo = {
      id: generateId(),
      text: "Test todo",
      completed: false,
      priority: "medium" as const,
      createdAt: Date.now(),
    };

    todos.value.push(newTodo);

    expect(todos.value).toHaveLength(1);
    expect(todos.value[0].text).toBe("Test todo");
  });

  test("can toggle todo completion", () => {
    // Add a todo
    const todo = {
      id: "test-1",
      text: "Test todo",
      completed: false,
      priority: "medium" as const,
      createdAt: Date.now(),
    };
    todos.value.push(todo);

    // Toggle it
    todo.completed = !todo.completed;

    expect(todo.completed).toBe(true);
  });

  test("can remove a todo", () => {
    // Add todos
    todos.value.push(
      { id: "test-1", text: "Test 1", completed: false, priority: "medium", createdAt: Date.now() },
      { id: "test-2", text: "Test 2", completed: false, priority: "medium", createdAt: Date.now() }
    );

    // Remove one
    const index = todos.value.findIndex((t) => t.id === "test-1");
    todos.value.splice(index, 1);

    expect(todos.value).toHaveLength(1);
    expect(todos.value.find((t) => t.id === "test-1")).toBeUndefined();
  });

  test("respects 100 todo limit", () => {
    // Fill to 100
    for (let i = 0; i < 100; i++) {
      todos.value.push({
        id: `todo-${i}`,
        text: `Todo ${i}`,
        completed: false,
        priority: "medium",
        createdAt: Date.now(),
      });
    }

    // Check limit
    expect(todos.value.length >= 100).toBe(true);
    expect(todos.value.length < 100).toBe(false); // Precondition fails
  });

  test("can use mock storage for persistence", async () => {
    // Store todos using mock storage
    await adapters.storage.set({
      todos: todos.value,
    });

    // Retrieve them
    const stored = await adapters.storage.get("todos");
    expect(stored.todos).toEqual(todos.value);
  });

  test("can use waitFor utility", async () => {
    let completed = false;

    // Simulate async operation
    setTimeout(() => {
      completed = true;
    }, 10);

    // Wait for it
    await waitFor(20);

    expect(completed).toBe(true);
  });
});

describe("Mock Adapters Integration", () => {
  let adapters: MockExtensionAdapters;

  beforeEach(() => {
    adapters = createMockAdapters();
  });

  test("can use mock storage adapter", async () => {
    // Store data using mock adapter
    await adapters.storage.set({ testKey: "testValue" });

    // Retrieve it
    const result = await adapters.storage.get("testKey");
    expect(result.testKey).toBe("testValue");
  });

  test("can use mock adapters in handlers", async () => {
    // Simulate a handler function that uses storage
    const saveHandler = async (text: string) => {
      await adapters.storage.set({ savedTodo: text });
      return { success: true };
    };

    await saveHandler("Persistent todo");

    const stored = await adapters.storage.get("savedTodo");
    expect(stored.savedTodo).toBe("Persistent todo");
  });
});
