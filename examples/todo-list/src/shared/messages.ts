import type { AppState, Todo, User } from "./types";

// Phantom type that embeds response type into message type
// The __response field is never actually used at runtime - it's purely for TypeScript
type Message<TType extends string, TPayload, TResponse> = TPayload & {
  type: TType;
  readonly __response?: TResponse;
};

export type TodoMessages =
  | Message<
      "USER_LOGIN",
      { userId: string; name: string; role: "user" | "admin" },
      { success: true; user: User }
    >
  | Message<"USER_LOGOUT", Record<string, never>, { success: true }>
  | Message<"TODO_ADD", { text: string }, { success: true; todo: Todo }>
  | Message<
      "TODO_TOGGLE",
      { id: string },
      { success: true; todo: Todo } | { success: false; error: string }
    >
  | Message<"TODO_REMOVE", { id: string }, { success: true }>
  | Message<"TODO_CLEAR_COMPLETED", Record<string, never>, { success: true; removed: number }>
  | Message<"GET_STATE", Record<string, never>, AppState>
  | Message<"GET_TODOS", { filter?: "all" | "active" | "completed" }, { todos: Todo[] }>;
