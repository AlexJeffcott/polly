// Application state management using Polly's reactive state primitives
import { $sharedState } from "@fairfox/polly/state";
import type { Todo, User } from "../shared/types";

// Reactive state with automatic synchronization and persistence
export const user = $sharedState<User>("user", {
  id: null,
  name: "Guest",
  role: "guest",
  loggedIn: false,
});

export const todos = $sharedState<Todo[]>("todos", []);

export const filter = $sharedState<"all" | "active" | "completed">("filter", "all");

// Configurable todo limit (exercises { type: "number" } verification)
export const maxTodos = $sharedState<number>("maxTodos", 50);

// Helper to generate IDs
export function generateId(): string {
  return `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
}
