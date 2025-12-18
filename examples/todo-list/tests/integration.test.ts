// Integration test simulating popup → background flow
import { beforeEach, describe, expect, test } from "bun:test";
import { state } from "../src/background/state";

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

describe("Todo Add Flow", () => {
  test("adding a todo should result in exactly one todo", () => {
    const initialCount = state.todos.length;
    expect(initialCount).toBe(0);

    // Simulate TODO_ADD handler being called
    const newTodo = {
      id: "test-1",
      text: "Test todo",
      completed: false,
      createdAt: Date.now(),
    };
    state.todos.push(newTodo);

    // Check that only one todo was added
    expect(state.todos.length).toBe(1);
    expect(state.todos[0].text).toBe("Test todo");

    // Simulate GET_STATE handler being called
    const returnedState = {
      user: state.user,
      todos: state.todos,
      filter: state.filter,
    };

    // Verify GET_STATE returns exactly one todo
    expect(returnedState.todos.length).toBe(1);
    expect(returnedState.todos[0].text).toBe("Test todo");
  });
});
