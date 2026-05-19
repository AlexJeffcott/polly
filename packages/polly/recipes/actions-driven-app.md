# actions-driven-app

> I want a Polly app where every state mutation flows through typed action
> handlers and components stay logic-free.

A code-along for the three-layer split that `@fairfox/polly/actions` exists
to support: event delegation on the document, one typed registry that owns
every mutation, stores whose public surface is signals and named methods.

## The loop you are building

One click-to-render cycle flows:

1. A user clicks a button with `data-action="todo:toggle"`.
2. The document listener catches it, walks up to the `[data-action]`
   ancestor, and parses `data-action-*` attributes into a data object.
3. The matching handler in your registry runs, calls
   `stores.todos.toggle(id)`.
4. The store's `todos` signal changes.
5. Every component reading `todos.value` re-renders.

No callback threads through props. No component calls a store method
directly. The registry is the only place where state mutates.

## Stores

A store is a typed bag of signals with methods. Methods are the one public
mutation surface; components read the signals and dispatch actions. The
`createStore` helper is a marker — the value is a plain object.

```ts
import { createStore } from "@fairfox/polly/actions";
import { $persistedState } from "@fairfox/polly/state";
import { computed } from "@preact/signals";

export function makeTodoStore() {
  const todos = $persistedState<Todo[]>("todos", []);

  function add(title: string): void {
    const trimmed = title.trim();
    if (trimmed === "") return;
    todos.value = [...todos.value, { id: crypto.randomUUID(), title: trimmed, done: false }];
  }

  function toggle(id: string): void {
    todos.value = todos.value.map(t => t.id === id ? { ...t, done: !t.done } : t);
  }

  return createStore({
    todos,
    remaining: computed(() => todos.value.filter(t => !t.done).length),
    add,
    toggle,
  });
}
```

One store per cohesive slice of domain. A `makeRootStore()` function
composes them into the bag you pass to `<StoreProvider>`.

## Forms

`createForm` takes a name, initial values, and `onSubmit`. It returns per-
field signals, an aggregated `values` signal, `open` / `close` / `submit`
methods, and a set of auto-registered action handlers (`{name}:open`,
`{name}:close`, `{name}:submit`) you spread into your registry.

```ts
import { createForm } from "@fairfox/polly/actions";

export const createTodoForm = createForm({
  name: "todo:create",
  initialValues: { title: "" },
  validate: v => v.title.trim() === "" ? { title: "Title required" } : null,
  onSubmit: async ({ values, stores }) => {
    stores.todos.add(values.title);
  },
});
```

Two other hooks earn their place as the app grows. `onOpen` pre-populates
from an entity the modal edits. `guard` returns a boolean; when it turns
false while the form is open, the form closes itself — the canonical fix
for "the user opened the edit modal, then deleted the entity from another
tab".

## The action registry

One object, typed against your root-store shape, composed by spreading
form actions and adding domain handlers. All business logic lives here.

```ts
import type { ActionRegistry } from "@fairfox/polly/actions";
import { createTodoForm } from "./forms";
import type { RootStore } from "./stores";

export const ACTION_REGISTRY: ActionRegistry<RootStore> = {
  ...createTodoForm.actions,

  "todo:toggle": ({ data, stores }) => {
    const id = data.todoId;
    if (id) stores.todos.toggle(id);
  },

  "theme:toggle": ({ stores }) => {
    stores.view.toggleTheme();
  },
};
```

Action names are namespaced (`modal:show`, `todo:toggle`, `team:create`).
The convention keeps a large registry grep-able. Pick a delimiter and
hold the line.

## Entry point

`main.tsx` owns five lines of setup: build the store bag, late-bind any
forms that need it, install the delegation, mount the provider, render.

```tsx
import { installEventDelegation, StoreProvider, submitError } from "@fairfox/polly/actions";
import { render } from "preact";
import { ACTION_REGISTRY } from "./actions";
import { createTodoForm } from "./forms";
import { makeRootStore } from "./stores";
import { App } from "./App";

const stores = makeRootStore();
createTodoForm.bindStores(() => stores);

installEventDelegation(async (dispatch) => {
  const handler = ACTION_REGISTRY[dispatch.action];
  if (!handler) return;
  try {
    await handler({ stores, ...dispatch });
  } catch (err) {
    submitError(dispatch.action, err);
  }
});

const root = document.getElementById("app");
if (!root) throw new Error("missing #app mount point");
render(<StoreProvider stores={stores}><App /></StoreProvider>, root);
```

The `submitError` wrapper is the contract with the rest of the runtime:
any thrown error lands on the global `errorState` signal, which your
`<Toast.Viewport />` renders without further wiring.

## Components

Components read signals via `useStores()` and emit markup. They never
mutate state, never take callbacks for domain operations, never import
from `./actions`.

```tsx
<button data-action="todo:toggle" data-action-todo-id={todo.id}>
  {todo.done ? "Undo" : "Done"}
</button>
```

`data-action-*` attributes are camel-cased by the parser —
`data-action-todo-id` becomes `data.todoId`. That is your whole payload
shape. For anything richer (the current value of an input, say), read it
on the element inside the handler, or use `<ActionForm>` and let the
`:submit` handler receive `FormData`.

## The error surface

`errorState` is a signal the runtime owns. `submitError(action, err)`
appends an entry; `setError(message, { severity })` is the handler-facing
shortcut; `<Toast.Viewport />` from `@fairfox/polly/ui` consumes the
signal and auto-dismisses after five seconds (hover pauses the timer).

Stop reaching for `try/catch` inside every handler — let the wrapper in
`main.tsx` catch, and reach for `submitError` only when a handler needs
to surface a controlled failure before it throws.

## Testing handlers

The runtime exposes a DOM-less harness. `runAction` invokes a handler by
name with a fake context; `createMockStores` wraps a partial object of
signal-backed fakes.

```ts
import { runAction } from "@fairfox/polly/actions";
import { signal } from "@preact/signals";
import { ACTION_REGISTRY } from "../src/actions";

test("todo:toggle forwards the id", async () => {
  const calls: string[] = [];
  const stores = {
    todos: { todos: signal([]), toggle: (id: string) => { calls.push(id); } },
  } as unknown as RootStore;

  await runAction(ACTION_REGISTRY, "todo:toggle", {
    stores,
    data: { todoId: "abc" },
  });

  expect(calls).toEqual(["abc"]);
});
```

This is the whole test surface you need for handler logic. Browser
behaviour — focus traps, overlay stacking, form-submit dispatch — is
covered by the primitives and has its own browser-harness tests in the
Polly repo.

## When to reach for the pattern

The cost is a tier of indirection: you write a `data-action` attribute
and a handler entry instead of one `onClick`. The payoff is that every
mutation in the app is in one place, reachable by grep, testable without
a component tree, and typed against a single store shape.

Reach for it when handler-like code has started repeating across
components, when state mutations are hidden inside callbacks threaded
through three layers of props, or when a refactor needs to answer "where
does state change?" and the answer is too many places to list.

## What this guide doesn't cover

The recipe stops at the loop. Choosing a bundler, choosing a router,
choosing how your `<App>` composes its own components — all of those are
independent of the action pattern. Follow-up recipes cover specific
deployment shapes (`mesh-only-cloudflare`, `mesh-pi-peer`) that stand on
top of this pattern; the `docs/ACTIONS.md` reference expands on each
primitive's options.
