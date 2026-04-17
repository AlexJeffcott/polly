/**
 * Form lifecycle tests — exercise createTodoForm in isolation.
 */

import { beforeEach, expect, test } from "bun:test";
import { signal } from "@preact/signals";
import { createTodoForm } from "../src/forms.ts";
import type { RootStore, Todo } from "../src/stores.ts";

function makeStores(): RootStore & { _calls: unknown[] } {
  const todos = signal<Todo[]>([]);
  const calls: unknown[] = [];
  const stub = {
    todos: {
      todos,
      remaining: { value: 0 } as unknown as RootStore["todos"]["remaining"],
      add: (title: string) => {
        calls.push({ name: "add", title });
      },
      rename: () => undefined,
      toggle: () => undefined,
      remove: () => undefined,
    },
    view: {
      theme: signal<"light" | "dark">("light"),
      selectedId: signal<string | null>(null),
      toggleTheme: () => undefined,
      select: () => undefined,
    },
    _calls: calls,
  } as unknown as RootStore & { _calls: unknown[] };
  createTodoForm.bindStores(() => stub);
  return stub;
}

beforeEach(() => {
  createTodoForm.close();
});

test("blank title is rejected by validate and add is not called", async () => {
  const stores = makeStores();
  createTodoForm.open();
  createTodoForm.fields.title.value = "   ";
  await createTodoForm.submit();
  expect(createTodoForm.errors.value.title).toBe("Title required");
  expect(stores._calls).toEqual([]);
  expect(createTodoForm.isOpen.value).toBe(true);
});

test("valid title calls stores.todos.add and closes the form", async () => {
  const stores = makeStores();
  createTodoForm.open();
  createTodoForm.fields.title.value = "Buy milk";
  await createTodoForm.submit();
  expect(stores._calls).toEqual([{ name: "add", title: "Buy milk" }]);
  expect(createTodoForm.isOpen.value).toBe(false);
});
