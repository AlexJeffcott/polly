# Actions

One listener. One typed registry. Components read signals and emit markup.
`@fairfox/polly/actions` ships the runtime.

## When to use actions

Reach for the actions layer when your components are mutating state directly
— calling store methods in event handlers, threading callbacks through
deeply nested props, or scattering identical event-handling logic across
many files. Centralise the logic in one registry, let components stay
logic-free, get typed handlers and a single testing surface in return.

Do not reach for actions when state flows one way and your components are
already thin views over signals. The pattern pays off once the handler
surface grows past a handful.

## Three layers

Every actions-driven app has the same three parts.

**Event delegation.** One document listener catches click, submit, change,
input, keydown. It walks up the DOM with `closest('[data-action]')`, parses
`data-action-*` attributes into a camelCase object, and dispatches to a
named handler. Forms fire their action on submit only. Enter and Space
activate non-interactive elements that carry `data-action`. Escape pops
the topmost overlay.

**Action registry.** A typed map from action name to handler. Each handler
receives `{ stores, event, element, data }` and returns void or a Promise.
All business logic lives here; components never mutate state directly.

**Stores.** Typed bags of signals plus methods. Methods are the only
mutation surface: actions call them; components read the signals they
expose. The store bag is wired into Preact context via `StoreProvider`,
reached from any component with `useStores()`.

```ts
import {
  installEventDelegation, type ActionRegistry, type ActionContext,
} from '@fairfox/polly/actions';

const ACTION_REGISTRY: ActionRegistry<RootStore> = {
  'theme:toggle': ({ stores }) => { stores.ui.toggleTheme(); },
  'team:create': async ({ data, stores }) => {
    await stores.data.createTeam({ name: data.name });
  },
};

installEventDelegation((dispatch) => {
  const handler = ACTION_REGISTRY[dispatch.action];
  handler?.(ctxFor(dispatch, stores));
});
```

Components emit:

```tsx
<button data-action="theme:toggle">Toggle theme</button>
<button data-action="team:create" data-action-name="Alpha">New team</button>
```

## Forms

`createForm` is the specialisation of `createStore` most apps reach for.
Each form exposes per-field signals, an aggregated values signal, methods
(`open`, `close`, `submit`), and three auto-registered action handlers
(`{name}:open`, `{name}:close`, `{name}:submit`). Spread `.actions` into
the registry and the form responds to `<button data-action="team:open">`
and `<form data-action="team:submit">` out of the box.

```ts
const teamForm = createForm<TeamValues, RootStore>({
  name: 'team',
  initialValues: { name: '', description: '' },
  guard: ({ stores }) =>
    stores.data.teams.value.some(t => t.id === stores.view.modalEntityId),
  onOpen: ({ data, stores }) => {
    const id = data.entityId;
    const existing = stores.data.teams.value.find(t => t.id === id);
    return existing ? { name: existing.name } : {};
  },
  onSubmit: async ({ values, stores }) => {
    await stores.data.createTeam(values);
  },
});

const ACTION_REGISTRY: ActionRegistry<RootStore> = {
  ...teamForm.actions,
  'theme:toggle': ({ stores }) => stores.ui.toggleTheme(),
};
```

`guard` runs as an internal effect: if it returns false while the form is
open, the form closes automatically. Useful for "entity deleted
mid-edit" — a user editing a team whose subject disappears should not
stay on a dead form.

`createFormSet([formA, formB])` composes many forms: merged `.actions`,
a single `openForm` signal ("which form is open, if any"), and
`closeAll()` for cleanup. Apps with dozens of forms avoid repeating
the spread for every registry.

## Error surface

Actions that throw, and any handler that wants to surface a user-visible
message, route through the global `errorState` signal via `submitError`.
The Toast component in `@fairfox/polly/ui` consumes that signal
automatically; apps that want bespoke error rendering read it directly.

```ts
import { submitError } from '@fairfox/polly/actions';

const ACTION_REGISTRY: ActionRegistry<RootStore> = {
  'team:delete': async ({ data, stores }) => {
    try {
      await stores.data.deleteTeam(data.teamId);
    } catch (err) {
      submitError('team:delete', err);
    }
  },
};
```

## Testing

`runAction` invokes a handler in isolation. Construct a mock stores bag
with `createMockStores`, build a fake element with `createMockElement`
when a handler reads from `data-action-*` attributes, and wrap it all
with `runAction`. No jsdom, no browser harness, no document listener.

```ts
import { runAction } from '@fairfox/polly/actions';

test('team:create writes through to the store', async () => {
  const stores = createMockStores({
    data: { createTeam: mock() },
  });
  await runAction(ACTION_REGISTRY, 'team:create', {
    stores,
    data: { name: 'Alpha' },
  });
  expect(stores.data.createTeam).toHaveBeenCalledWith({ name: 'Alpha' });
});
```

For full-DOM coverage — focus trap, portal parentage, scroll lock — use
the Puppeteer harness at `@fairfox/polly/test/browser`. The unit-level
helpers here are for handler logic.

## Migrating an ad-hoc app

If an app has scattered `onClick` handlers mutating module-scope
signals, migrate one feature at a time. Pick a feature. Replace the
inline handler with a `data-action` attribute. Move the logic into the
registry. Hoist the feature's state from component scope to a store.
Delete the callback prop. Repeat.

The plumbing can coexist with bespoke callbacks during migration — the
event delegation only fires when it sees `data-action`; other clicks
flow through Preact as before. A gradual migration stays green at
every step.

## API reference

See the source at `src/actions/` for exact signatures; every export is
documented by a module-level docstring. The subpath is
`@fairfox/polly/actions`, and the TypeScript types resolve through the
usual editor tooling.
