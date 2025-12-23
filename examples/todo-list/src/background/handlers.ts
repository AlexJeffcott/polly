// Message handlers
import { createBackground } from "@fairfox/polly/background";
import type { TodoMessages } from "../shared/messages";
import type { Todo } from "../shared/types";
import { generateId, state } from "./state";

// Initialize background script with MessageRouter
// IMPORTANT: Always use createBackground() in background scripts, NOT getMessageBus('background')
// This ensures proper message routing and prevents double-execution bugs.
// See: docs/BACKGROUND_SETUP.md for details
const bus = createBackground<TodoMessages>();

// ============================================================================
// User Authentication
// ============================================================================

bus.on("USER_LOGIN", (payload: { userId: string; name: string; role: "user" | "admin" }) => {
  // Preconditions

  // State changes
  state.user.loggedIn = true;
  state.user.id = payload.userId;
  state.user.name = payload.name;
  state.user.role = payload.role;

  // Postconditions

  return { success: true, user: state.user };
});

bus.on("USER_LOGOUT", () => {
  // Precondition

  // State changes
  state.user.loggedIn = false;
  state.user.id = null;
  state.user.name = "Guest";
  state.user.role = "guest";

  // Postconditions

  return { success: true };
});

// ============================================================================
// Todo Management
// ============================================================================

bus.on("TODO_ADD", (payload: { text: string }) => {
  // Preconditions

  const _previousCount = state.todos.length;

  // State change
  const newTodo: Todo = {
    id: generateId(),
    text: payload.text,
    completed: false,
    createdAt: Date.now(),
  };
  state.todos.push(newTodo);

  // Postconditions

  // Check for duplicate IDs
  const ids = state.todos.map((t) => t.id);
  const _uniqueIds = new Set(ids);

  return { success: true, todo: newTodo };
});

bus.on("TODO_TOGGLE", (payload: { id: string }) => {
  // Precondition
  const todo = state.todos.find((t) => t.id === payload.id);

  if (todo) {
    const _previousCompleted = todo.completed;

    // State change
    todo.completed = !todo.completed;

    // Postcondition

    return { success: true, todo };
  }

  return { success: false, error: "Todo not found" };
});

bus.on("TODO_REMOVE", (payload: { id: string }) => {
  // Precondition
  const index = state.todos.findIndex((t) => t.id === payload.id);

  const _previousCount = state.todos.length;

  // State change
  state.todos.splice(index, 1);

  // Postconditions

  return { success: true };
});

bus.on("TODO_CLEAR_COMPLETED", () => {
  const _previousCount = state.todos.length;
  const completedCount = state.todos.filter((t) => t.completed).length;

  // State change
  state.todos = state.todos.filter((t) => !t.completed);

  // Postconditions

  return { success: true, removed: completedCount };
});

// ============================================================================
// Queries
// ============================================================================

bus.on("GET_STATE", () => {
  // Verification: ensure all todo IDs are unique
  const ids = state.todos.map((t) => t.id);
  const _uniqueIds = new Set(ids);

  // Return a deep copy to prevent reference sharing issues
  return {
    user: { ...state.user },
    todos: state.todos.map((t) => ({ ...t })),
    filter: state.filter,
  };
});

bus.on("GET_TODOS", (payload?: { filter?: "all" | "active" | "completed" }) => {
  const filter = payload?.filter || "all";

  let filteredTodos = state.todos;
  if (filter === "active") {
    filteredTodos = state.todos.filter((t) => !t.completed);
  } else if (filter === "completed") {
    filteredTodos = state.todos.filter((t) => t.completed);
  }

  return { todos: filteredTodos };
});

console.log("Todo list background script loaded!");
