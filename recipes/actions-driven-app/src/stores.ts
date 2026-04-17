/**
 * Stores: todo list (persisted), ephemeral view state.
 *
 * Exposes signals for reading and methods for mutation. Methods are
 * the only public mutation surface — actions call them; components
 * read signals and dispatch actions.
 */

import { $persistedState } from "@fairfox/polly/state";
import { createStore } from "@fairfox/polly/actions";
import { computed, signal } from "@preact/signals";

export type Todo = {
  id: string;
  title: string;
  done: boolean;
};

function makeTodoStore() {
  const todos = $persistedState<Todo[]>("recipe.todos", []);

  function add(title: string): void {
    const trimmed = title.trim();
    if (trimmed === "") return;
    todos.value = [
      ...todos.value,
      { id: crypto.randomUUID(), title: trimmed, done: false },
    ];
  }

  function rename(id: string, title: string): void {
    todos.value = todos.value.map((t) =>
      t.id === id ? { ...t, title } : t,
    );
  }

  function toggle(id: string): void {
    todos.value = todos.value.map((t) =>
      t.id === id ? { ...t, done: !t.done } : t,
    );
  }

  function remove(id: string): void {
    todos.value = todos.value.filter((t) => t.id !== id);
  }

  return createStore({
    todos,
    remaining: computed(
      () => todos.value.filter((t) => !t.done).length,
    ),
    add,
    rename,
    toggle,
    remove,
  });
}

function makeViewStore() {
  const theme = $persistedState<"light" | "dark">("recipe.theme", "light");
  const selectedId = signal<string | null>(null);

  function toggleTheme(): void {
    theme.value = theme.value === "dark" ? "light" : "dark";
  }

  function select(id: string | null): void {
    selectedId.value = id;
  }

  return createStore({ theme, selectedId, toggleTheme, select });
}

export type RootStore = ReturnType<typeof makeRootStore>;

export function makeRootStore() {
  return createStore({
    todos: makeTodoStore(),
    view: makeViewStore(),
  });
}
