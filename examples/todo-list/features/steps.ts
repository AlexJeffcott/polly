/**
 * Step bindings for the todo-list features.
 *
 * Each binding is dual-use: its given/when/then drive the REAL factory bus
 * (built in defineWorld via createBackground + the same registerTodoHandlers
 * the extension entry calls), and its message/stateExpr are read statically by
 * `polly bdd check` / `polly verify --witness`. Mechanics live here so the
 * .feature files stay declarative.
 */
import { createBackground, MessageRouter } from "@fairfox/polly/background";
import { defineStep, defineWorld, driveBus } from "@fairfox/polly/bdd";
import { createMockAdapters } from "@fairfox/polly/test";
import { registerTodoHandlers } from "../src/background/handlers";
import { filter, maxTodos, theme, todos, user } from "../src/background/state";
import type { TodoMessages } from "../src/shared/messages";
import type { Todo } from "../src/shared/types";

function todo(id: string, text: string, completed = false): Todo {
  return { id, text, completed, priority: "low", createdAt: 0 };
}

defineWorld({
  create() {
    // The documented factory path — never a hand-wired bus (polly#57).
    MessageRouter.resetInstance();
    const real = createBackground<TodoMessages>(createMockAdapters());
    registerTodoHandlers(real);
    return { bus: driveBus(real), signals: { user, todos, theme, filter, maxTodos }, vars: {} };
  },
  reset() {
    // Cold start before every scenario: every signal back to its initial value.
    user.value = { id: null, name: "Guest", role: "guest", loggedIn: false };
    todos.value = [];
    theme.value = "system";
    filter.value = "all";
    maxTodos.value = 50;
  },
});

// ── Given (and the dual-role "signed out", also a Then) ──

defineStep({
  pattern: "the user is signed out",
  given: () => {
    user.value = { id: null, name: "Guest", role: "guest", loggedIn: false };
  },
  then: () => {
    if (user.value.loggedIn) throw new Error("expected the user to be signed out");
  },
  stateExpr: "user.loggedIn === false",
});

defineStep({
  pattern: "the user is signed in as {string}",
  given: (_w, role) => {
    user.value = { id: "u0", name: "U", role: role as "user" | "admin", loggedIn: true };
  },
  stateExpr: "user.loggedIn === true",
});

defineStep({
  pattern: "the todo list is empty",
  given: () => {
    todos.value = [];
  },
  stateExpr: "todos",
});

defineStep({
  pattern: "a todo {string} exists",
  given: (w, text) => {
    todos.value = [todo("t1", text)];
    w.vars.todoId = "t1";
  },
  stateExpr: "todos",
});

defineStep({
  pattern: "a completed todo {string} and an active todo {string} exist",
  given: (_w, done, active) => {
    todos.value = [todo("t-done", done, true), todo("t-active", active, false)];
  },
  stateExpr: "todos",
});

// ── When ──

defineStep({
  pattern: "the user signs in as {string}",
  when: (w, role) => w.bus.send({ type: "USER_LOGIN", userId: "u1", name: "U", role }),
  message: "USER_LOGIN",
});

defineStep({
  pattern: "the user signs out",
  when: (w) => w.bus.send({ type: "USER_LOGOUT" }),
  message: "USER_LOGOUT",
});

defineStep({
  pattern: "the user attempts to sign in as a guest",
  when: (w) => w.bus.send({ type: "USER_LOGIN", userId: "u1", name: "U", role: "guest" }),
  message: "USER_LOGIN",
});

defineStep({
  pattern: "a todo {string} is added",
  when: (w, text) => w.bus.send({ type: "TODO_ADD", text, priority: "low" }),
  message: "TODO_ADD",
});

defineStep({
  pattern: "that todo is completed",
  when: (w) => w.bus.send({ type: "TODO_TOGGLE", id: w.vars.todoId }),
  message: "TODO_TOGGLE",
});

defineStep({
  pattern: "a todo with id {string} is completed",
  when: (w, id) => w.bus.send({ type: "TODO_TOGGLE", id }),
  message: "TODO_TOGGLE",
});

defineStep({
  pattern: "completed todos are cleared",
  when: (w) => w.bus.send({ type: "TODO_CLEAR_COMPLETED" }),
  message: "TODO_CLEAR_COMPLETED",
});

// ── Then ──

defineStep({
  pattern: "the user is signed in",
  then: () => {
    if (!user.value.loggedIn) throw new Error("expected the user to be signed in");
  },
  stateExpr: "user.loggedIn === true",
});

defineStep({
  pattern: "their role is {string}",
  then: (_w, role) => {
    if (user.value.role !== role) throw new Error(`expected role ${role}, got ${user.value.role}`);
  },
  stateExpr: "user.role",
});

defineStep({
  pattern: "the list contains {int} todo",
  then: (_w, count) => {
    const n = Number(count);
    if (todos.value.length !== n) throw new Error(`expected ${n} todos, got ${todos.value.length}`);
  },
  stateExpr: "todos.length",
});

defineStep({
  pattern: "the list contains the todo {string}",
  then: (_w, text) => {
    if (!todos.value.some((t) => t.text === text)) throw new Error(`"${text}" not in the list`);
  },
  stateExpr: "todos",
});

defineStep({
  pattern: "the list does not contain the todo {string}",
  then: (_w, text) => {
    if (todos.value.some((t) => t.text === text)) throw new Error(`"${text}" should be excluded`);
  },
  stateExpr: "todos",
});

defineStep({
  pattern: "that todo is marked done",
  then: (w) => {
    const t = todos.value.find((x) => x.id === w.vars.todoId);
    if (!t?.completed) throw new Error("expected the todo to be marked done");
  },
  stateExpr: "todos",
});

defineStep({
  pattern: "the change is refused",
  then: (w) => {
    const resp = w.lastResponse as { success?: boolean } | undefined;
    if (resp?.success !== false)
      throw new Error("expected the change to be refused (success: false)");
  },
});
