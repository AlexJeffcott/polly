// State-mutating functions with verification primitives
// These are called from route handlers in index.ts
import { ensures, requires } from "@fairfox/polly/verify";
import { authState, todoCount } from "./state";

export function login(userId: string) {
  requires(authState.value.loggedIn === false, "Must not be logged in");

  authState.value = { loggedIn: true, userId };

  ensures(authState.value.loggedIn === true, "Must be logged in after login");
  ensures(authState.value.userId === userId, "User ID must match");
}

export function logout() {
  requires(authState.value.loggedIn === true, "Must be logged in to logout");

  authState.value = { loggedIn: false, userId: null };

  ensures(authState.value.loggedIn === false, "Must be logged out after logout");
}

export function addTodo(_text: string) {
  requires(authState.value.loggedIn === true, "Must be logged in to add todos");
  requires(todoCount.value < 100, "Cannot exceed 100 todos");

  todoCount.value += 1;

  ensures(todoCount.value > 0, "Todo count must be positive after add");
}

export function removeTodo() {
  requires(todoCount.value > 0, "Must have todos to remove");

  todoCount.value -= 1;
}
