/**
 * Action-handler unit tests.
 *
 * Hand-rolled store fakes that satisfy the RootStore shape; runAction
 * invokes the handler with a fake ActionContext. No DOM, no render.
 */

import { beforeEach, expect, test } from "bun:test";
import { runAction } from "@fairfox/polly/actions";
import { signal } from "@preact/signals";
import { ACTION_REGISTRY } from "../src/actions.ts";
import { createTodoForm } from "../src/forms.ts";
import type { RootStore, Todo } from "../src/stores.ts";

type Stub = RootStore & {
  todos: RootStore["todos"] & {
    _calls: { name: string; args: unknown[] }[];
  };
};

function stubStores(initial: Todo[] = []): Stub {
  const todos = signal<Todo[]>(initial);
  const calls: { name: string; args: unknown[] }[] = [];
  const record =
    (name: string) =>
    (...args: unknown[]) => {
      calls.push({ name, args });
    };

  const stub = {
    todos: {
      todos,
      remaining: { value: 0 } as unknown as RootStore["todos"]["remaining"],
      add: record("add"),
      rename: record("rename"),
      toggle: record("toggle"),
      remove: record("remove"),
      _calls: calls,
    },
    view: {
      theme: signal<"light" | "dark">("light"),
      selectedId: signal<string | null>(null),
      toggleTheme: record("toggleTheme"),
      select: record("select"),
    },
  } as unknown as Stub;
  createTodoForm.bindStores(() => stub);
  return stub;
}

beforeEach(() => {
  createTodoForm.close();
});

test("todo:toggle forwards the id to stores.todos.toggle", async () => {
  const stores = stubStores();
  await runAction(ACTION_REGISTRY, "todo:toggle", {
    stores,
    data: { todoId: "abc" },
  });
  expect(stores.todos._calls).toEqual([{ name: "toggle", args: ["abc"] }]);
});

test("todo:remove forwards the id to stores.todos.remove", async () => {
  const stores = stubStores();
  await runAction(ACTION_REGISTRY, "todo:remove", {
    stores,
    data: { todoId: "abc" },
  });
  expect(stores.todos._calls).toEqual([{ name: "remove", args: ["abc"] }]);
});

test("todo:rename with blank value surfaces an error and does not mutate", async () => {
  const stores = stubStores();
  await runAction(ACTION_REGISTRY, "todo:rename", {
    stores,
    data: { todoId: "abc", value: "   " },
  });
  expect(stores.todos._calls).toEqual([]);
});
