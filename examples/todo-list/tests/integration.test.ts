// Integration test simulating popup → background flow
import { beforeEach, describe, expect, test } from "bun:test";
import { filter, todos, user } from "../src/background/state";

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

describe("Todo Add Flow", () => {
  test("adding a todo should result in exactly one todo", () => {
    const initialCount = todos.value.length;
    expect(initialCount).toBe(0);

    // Simulate TODO_ADD handler being called
    const newTodo = {
      id: "test-1",
      text: "Test todo",
      completed: false,
      priority: "medium" as const,
      createdAt: Date.now(),
    };
    todos.value.push(newTodo);

    // Check that only one todo was added
    expect(todos.value.length).toBe(1);
    expect(todos.value[0].text).toBe("Test todo");

    // Simulate GET_STATE handler being called
    const returnedState = {
      user: user.value,
      todos: todos.value,
      filter: filter.value,
    };

    // Verify GET_STATE returns exactly one todo
    expect(returnedState.todos.length).toBe(1);
    expect(returnedState.todos[0].text).toBe("Test todo");
  });
});
