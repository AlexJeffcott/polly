// Message handlers
import { createBackground } from "@fairfox/polly/background";
import type { TodoMessages } from "../shared/messages";
import type { Todo } from "../shared/types";
import { filter, generateId, todos, user } from "./state";

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

  // State changes - using reactive signals with automatic sync
  user.value = {
    loggedIn: true,
    id: payload.userId,
    name: payload.name,
    role: payload.role,
  };

  // Postconditions

  return { success: true, user: user.value };
});

bus.on("USER_LOGOUT", () => {
  // Precondition

  // State changes - using reactive signals with automatic sync
  user.value = {
    loggedIn: false,
    id: null,
    name: "Guest",
    role: "guest",
  };

  // Postconditions

  return { success: true };
});

// ============================================================================
// Todo Management
// ============================================================================

bus.on("TODO_ADD", (payload: { text: string }) => {
  // Preconditions

  const _previousCount = todos.value.length;

  // State change - using reactive signals with automatic sync
  const newTodo: Todo = {
    id: generateId(),
    text: payload.text,
    completed: false,
    createdAt: Date.now(),
  };
  todos.value = [...todos.value, newTodo];

  // Postconditions

  // Check for duplicate IDs
  const ids = todos.value.map((t) => t.id);
  const _uniqueIds = new Set(ids);

  return { success: true, todo: newTodo };
});

bus.on("TODO_TOGGLE", (payload: { id: string }) => {
  // Precondition
  const todo = todos.value.find((t) => t.id === payload.id);

  if (todo) {
    const _previousCompleted = todo.completed;

    // State change - using reactive signals with automatic sync
    todos.value = todos.value.map((t) =>
      t.id === payload.id ? { ...t, completed: !t.completed } : t
    );

    // Postcondition
    const updatedTodo = todos.value.find((t) => t.id === payload.id);
    if (!updatedTodo) {
      return { success: false, error: "Todo not found after update" };
    }

    return { success: true, todo: updatedTodo };
  }

  return { success: false, error: "Todo not found" };
});

bus.on("TODO_REMOVE", (payload: { id: string }) => {
  // Precondition
  const _index = todos.value.findIndex((t) => t.id === payload.id);

  const _previousCount = todos.value.length;

  // State change - using reactive signals with automatic sync
  todos.value = todos.value.filter((t) => t.id !== payload.id);

  // Postconditions

  return { success: true };
});

bus.on("TODO_CLEAR_COMPLETED", () => {
  const _previousCount = todos.value.length;
  const completedCount = todos.value.filter((t) => t.completed).length;

  // State change - using reactive signals with automatic sync
  todos.value = todos.value.filter((t) => !t.completed);

  // Postconditions

  return { success: true, removed: completedCount };
});

// ============================================================================
// Queries
// ============================================================================

bus.on("GET_STATE", () => {
  // Verification: ensure all todo IDs are unique
  const ids = todos.value.map((t) => t.id);
  const _uniqueIds = new Set(ids);

  // Return a deep copy to prevent reference sharing issues
  return {
    user: { ...user.value },
    todos: todos.value.map((t) => ({ ...t })),
    filter: filter.value,
  };
});

bus.on("GET_TODOS", (payload?: { filter?: "all" | "active" | "completed" }) => {
  const filterValue = payload?.filter || "all";

  let filteredTodos = todos.value;
  if (filterValue === "active") {
    filteredTodos = todos.value.filter((t) => !t.completed);
  } else if (filterValue === "completed") {
    filteredTodos = todos.value.filter((t) => t.completed);
  }

  return { todos: filteredTodos };
});

console.log("Todo list background script loaded!");
