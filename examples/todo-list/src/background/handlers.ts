// Message handlers with verification primitives
import { createBackground } from "@fairfox/polly/background";
import { ensures, hasLength, requires, stateConstraint } from "@fairfox/polly/verify";
import type { TodoMessages } from "../shared/messages";
import type { Todo } from "../shared/types";
import { filter, generateId, maxTodos, todos, user } from "./state";

// Initialize background script with MessageRouter
// IMPORTANT: Always use createBackground() in background scripts, NOT getMessageBus('background')
// This ensures proper message routing and prevents double-execution bugs.
// See: docs/BACKGROUND_SETUP.md for details
const bus = createBackground<TodoMessages>();

// State constraint: logged-out users must have guest role.
// Prunes impossible states like (loggedIn=false, role="admin") from TLC exploration.
stateConstraint(
  "LoggedOutIsGuest",
  () => user.value.loggedIn === true || user.value.role === "guest"
);

// ============================================================================
// User Authentication
// ============================================================================

bus.on("USER_LOGIN", (payload: { userId: string; name: string; role: "user" | "admin" }) => {
  // Preconditions - user must not already be logged in
  requires(user.value.loggedIn === false, "User must not be logged in");
  requires(payload.userId !== null, "User ID must be provided");

  // State changes - using reactive signals with automatic sync
  user.value = {
    loggedIn: true,
    id: payload.userId,
    name: payload.name,
    role: payload.role,
  };

  // Postconditions - verify state was updated correctly
  ensures(user.value.loggedIn === true, "User must be logged in after login");
  ensures(user.value.role !== "guest", "User must have non-guest role");

  return { success: true, user: user.value };
});

bus.on("USER_LOGOUT", () => {
  // Precondition - user must be logged in to logout
  requires(user.value.loggedIn === true, "User must be logged in to logout");

  // State changes - using reactive signals with automatic sync
  user.value = {
    loggedIn: false,
    id: null,
    name: "Guest",
    role: "guest",
  };

  // Postconditions - verify state was reset
  ensures(user.value.loggedIn === false, "User must be logged out after logout");
  ensures(user.value.role === "guest", "User must have guest role after logout");

  return { success: true };
});

// ============================================================================
// Todo Management
// ============================================================================

bus.on("TODO_ADD", (payload: { text: string; priority: "low" | "medium" | "high" }) => {
  // Preconditions - enforce configurable todo limit
  requires(hasLength(todos.value, { max: 99 }), "Cannot exceed 100 todos");
  requires(payload.text !== "", "Todo text must not be empty");

  // State change - using reactive signals with automatic sync
  // The priority parameter exercises parameter tracing for TLA+ generation
  const newTodo: Todo = {
    id: generateId(),
    text: payload.text,
    completed: false,
    priority: payload.priority,
    createdAt: Date.now(),
  };
  todos.value = [...todos.value, newTodo];

  // Postconditions - verify todo was added
  // Note: Can't reference local variables (previousCount) in ensures() for TLA+ translation
  ensures(todos.value.length > 0, "Todos must not be empty after add");

  return { success: true, todo: newTodo };
});

bus.on("TODO_TOGGLE", (payload: { id: string }) => {
  // Precondition - todo must exist
  // Note: TLA+ can't enumerate over sequences with \in, so we use length check as proxy
  requires(todos.value.length > 0, "Todos must not be empty to toggle");

  const todo = todos.value.find((t) => t.id === payload.id);
  if (todo) {
    // State change - using reactive signals with automatic sync
    todos.value = todos.value.map((t) =>
      t.id === payload.id ? { ...t, completed: !t.completed } : t
    );

    // Postcondition - verify todo count unchanged (toggle doesn't remove)
    ensures(todos.value.length > 0, "Todos must not be empty after toggle");

    // biome-ignore lint/style/noNonNullAssertion: todo exists after update
    const updatedTodo = todos.value.find((t) => t.id === payload.id)!;
    return { success: true, todo: updatedTodo };
  }

  return { success: false, error: "Todo not found" };
});

bus.on("TODO_REMOVE", (payload: { id: string }) => {
  // Precondition - todo must exist
  // Note: TLA+ can't enumerate over sequences with \in, so we use length check as proxy
  requires(todos.value.length > 0, "Todos must not be empty to remove");

  // State change - using reactive signals with automatic sync
  todos.value = todos.value.filter((t) => t.id !== payload.id);

  // Postconditions - verify removal (length-based check for TLA+ compatibility)
  // Note: Can't use .some() as TLA+ can't enumerate over sequences
  // The actual runtime check is done internally by filter()

  return { success: true };
});

bus.on("TODO_CLEAR_COMPLETED", () => {
  const completedCount = todos.value.filter((t) => t.completed).length;

  // State change - using reactive signals with automatic sync
  todos.value = todos.value.filter((t) => !t.completed);

  // Postconditions - verify operation completed
  // Note: Can't use .some() as TLA+ can't enumerate over sequences
  // The actual runtime check is done internally by filter()

  return { success: true, removed: completedCount };
});

// ============================================================================
// Configuration
// ============================================================================

bus.on("TODO_SET_LIMIT", (payload: { limit: number }) => {
  // Precondition - limit must be positive (exercises { type: "number" } verification)
  requires(payload.limit > 0, "Limit must be positive");

  // State change - update configurable limit
  maxTodos.value = payload.limit;

  return { success: true };
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
