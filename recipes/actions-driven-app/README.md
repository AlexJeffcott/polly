# actions-driven-app

> I want a Polly app where every state mutation flows through typed
> action handlers and components stay logic-free.

A minimal todo list demonstrating the full `@fairfox/polly/actions` +
`@fairfox/polly/ui` loop end to end.

## What's in it

- **Stores** (`src/stores.ts`) — one store for the todo list (backed by
  `$persistedState`), one for view state. Methods are the only
  mutation surface.
- **Forms** (`src/forms.ts`) — one `createForm` for the create-todo
  modal, with a validator that rejects blank titles.
- **Action registry** (`src/actions.ts`) — five entries (plus the three
  auto-registered from the form). All business logic lives here.
- **Components** (`src/App.tsx`) — Layout for structure, Modal for the
  create dialog, ActionForm + TextInput for the form, ActionInput for
  inline-edit of todo titles, Toast for errors. Every component reads
  signals and emits `data-action` markup. No callbacks.
- **Entry point** (`src/main.tsx`) — stores bag, form binding,
  `installEventDelegation`, `StoreProvider`, `render`.

## The loop

Every click-to-change-to-render flows:

1. User clicks a button with `data-action="todo:toggle"`
2. The document listener picks it up, parses `data-action-*` attrs
3. The matching entry in `ACTION_REGISTRY` runs, calls
   `stores.todos.toggle(id)`
4. The store's `todos` signal changes
5. Every component reading `todos.value` re-renders

## Running locally

```sh
bun install
bun test tests
bunx tsc --noEmit
```

The recipe ships without a bundler wired up — adopt any (Bun, Vite,
Rollup) and point it at `src/main.tsx`. The structural CSS, theme
tokens, and per-component styles are three separate imports in
`main.tsx` so consumers can opt out of the defaults.

## What it's for

Copy this folder into a new app; the skeleton is ready to grow. Add
stores to `makeRootStore()`, add forms next to their features, add
action handlers for any new interaction, render through the compound
primitives. The three-layer split (delegation, registry, stores)
stays intact no matter how many features you add.

## What it deliberately doesn't cover

- **Deployment shape** — follow-up recipes handle Cloudflare Pages,
  Raspberry Pi mesh peers, and other goal-shaped deploy targets.
- **Routing** — the action registry dispatches events, not routes.
  Pick any router; the pattern doesn't know about URLs.
- **Domain-specific styling** — the default theme is sane, not
  branded. Override `--polly-*` tokens for the look of your app.
