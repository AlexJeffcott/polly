# UI primitives

`@fairfox/polly/ui` provides a set of components built on the
action-registry runtime. Polly owns accessibility and structure;
consumers own visual values.

The full export list lives in `src/polly-ui/index.ts`. At time of
writing it includes `ActionForm`, `ActionInput`, `ActionSelect`,
`Badge`, `Button`, `Card`, `Checkbox`, `Cluster`, `Code`,
`Collapsible`, `ConfirmDialog` (plus the `confirm()` helper),
`Dropdown`, `Layout`, `Modal`, `OverlayRoot` (plus
`getOverlayRootNode`), `Select`, `Skeleton`, `Surface`, `Tabs`, `Text`,
`TextInput`, `Toast`, `Toggle`, and a markdown subpath. New components
land regularly; check the source if you need the current set.

## Import

```ts
import {
  Layout, Modal, ActionForm, TextInput, ActionInput,
  ConfirmDialog, Toast, OverlayRoot,
} from '@fairfox/polly/ui';

import '@fairfox/polly/ui/styles.css';      // structural + a11y
import '@fairfox/polly/ui/theme.css';       // default tokens — override or replace
import '@fairfox/polly/ui/components.css';  // per-component styles
```

## Theming contract

Two stylesheets exist because two kinds of CSS exist in this library.

`styles.css` carries the rules that must not be overridden. Focus ring,
minimum hit targets, scroll lock, overlay stacking, and reduced-motion
handling all live here. Apps that want different visuals override
`theme.css` or redefine individual variables; they should not touch
`styles.css`. If you find yourself wanting to override something in
`styles.css`, that is a signal to file an issue rather than work around
the cascade.

`theme.css` carries semantic tokens. Every surface, border, text colour,
accent, focus ring, space, radius, motion duration, font stack, and
typography size is a `--polly-*` variable. Both the light palette
(default) and the dark palette (under `prefers-color-scheme: dark`) pass
WCAG AA contrast against their surface. An ancestor element with
`data-polly-theme="dark"` or `data-polly-theme="light"` forces that mode
regardless of system preference.

To re-theme, define the variables in a higher cascade layer or in your
own stylesheet loaded after `theme.css`:

```css
:root {
  --polly-accent: #d64045;
  --polly-accent-contrast: #fff;
  --polly-radius-md: 2px;
  --polly-font-sans: "Inter", system-ui, sans-serif;
}
```

## The primitives

### Layout

The only component that owns layouting concerns. CSS Grid under the hood,
configured through props that map to CSS custom properties. The
`polly quality css-layout` check enforces "no `display: flex|grid`
outside Layout" across app CSS; use `/* layout-ignore */` to suppress
one-off cases.

```tsx
<Layout columns="1fr 2fr" gap="var(--polly-space-lg)" padding="var(--polly-space-md)">
  <aside>nav</aside>
  <main>content</main>
</Layout>
```

Props of interest: `rows`, `columns`, `gap`, `padding`, `stackOnMobile`
(collapse to a single column at ≤640px), `justifyItems`, `alignItems`,
`contents` (display: contents for transparent nesting), `subgrid`.

### Cluster

The second (and final) layout primitive — the `flex-wrap` counterpart to
`Layout`. Where `Layout` owns CSS Grid tracks, `Cluster` owns a row of
items that differ in width and must reflow as space runs out: filter
chips, tag and badge lists, groups of small buttons. The row wraps
automatically at narrow widths; items keep even spacing on both axes via
`gap`. A consumer never writes `display: flex` themselves — grid goes
through `Layout`, a wrapping row goes through `Cluster`.

```tsx
<Cluster gap="var(--polly-space-xs)">
  {tags.map((t) => <Badge key={t}>{t}</Badge>)}
</Cluster>
```

Props: `gap`, `padding`, `justify` (main-axis distribution), `align`
(cross-axis alignment, default `center`), `inline` (render as
`inline-flex`), `as` (polymorphic element). Like `Layout`, each maps to a
CSS custom property so consumers can override it in a media query.

### Text

Typographic primitive for secondary and sized copy — subtitles,
captions, field labels, empty-state text. Renders without a `style`
attribute or a hand-rolled `.muted` class. `tone` (`default` | `muted`)
and `size` (`xs` | `sm` | `md` | `lg` | `xl`, token-backed) drive the
visual values; `weight` (`normal` | `medium` | `bold`) is optional; `as`
keeps it polymorphic so the same primitive backs a `<span>`, `<p>`,
`<label>`, or `<figcaption>`. A no-prop `<Text>` is a plain `<span>`.

```tsx
<Text tone="muted" size="sm">Last edited 2 minutes ago</Text>
<Text as="label" htmlFor="email" weight="medium">Email</Text>
```

### Code

Inline monospace code span — `<code>` with the `--polly-font-mono`
stack, a faint sunken tint, and snug padding, so a consumer never
hand-rolls a `.mono` class for inline code or identifiers. Pass `block`
for a pre-wrapped `<pre><code>` code block. (A bare `<code>` also picks
up the monospace font from `styles.css`; `Code` adds the pill
treatment.)

```tsx
Run <Code>polly verify</Code> to check the spec.
```

### Modal

Compound dialog with focus trap, Escape handling, portal into
`OverlayRoot`, scroll lock, stacking. Root takes a signal for open state.
Focus moves inside on open and returns to the opener on close. Tab and
Shift+Tab are trapped. Escape pops the topmost overlay through the
registry.

```tsx
<Modal.Root when={form.isOpen} onClose={() => form.close()}>
  <Modal.Backdrop />
  <Modal.Content>
    <Modal.Header>
      <Modal.Title>Edit team</Modal.Title>
      <Modal.Close>Close</Modal.Close>
    </Modal.Header>
    <Modal.Body>…</Modal.Body>
    <Modal.Footer>…</Modal.Footer>
  </Modal.Content>
</Modal.Root>
```

`Modal.Close` accepts an optional `action` prop to dispatch a named
action instead of calling the onClose callback. Useful when the close
semantics need to live in the registry.

### ActionForm

Wraps `<form>` and sets `data-action="{form.name}:submit"` so the event
delegation reaches the form's auto-registered submit handler. Mirrors
`isSubmitting` onto `aria-busy` so consumer styling can respond without
extra wiring.

```tsx
<ActionForm form={teamForm}>
  <TextInput name="name" required />
  <button type="submit">Save</button>
</ActionForm>
```

### TextInput

Passive, token-styled native `<input>` or `<textarea>` (via `variant`).
Signal-backed: pass a plain string for uncontrolled (FormData picks up
the value on submit) or a `Signal<string>` for controlled. `invalid`
flips `aria-invalid` and `data-state="invalid"` for styling hooks.

### ActionInput

Dual-mode view/edit with action dispatch on commit. View mode renders
the current value as text; click, Enter, or Space enters edit mode;
`saveOn` picks the commit trigger (`blur`, `enter`, `cmd-enter`,
`explicit`, `input`). Commit fires the configured action with a
synthetic hidden element carrying `data-action-value`, so the existing
delegation picks it up. View and edit modes share padding, border width,
font, and line-height so toggling between them causes zero layout shift.

`saveOn="input"` is the live, filter-as-you-type mode: the field starts
in edit mode, stays editable, and commits the action on every keystroke
— no view/edit toggle. `inputType` sets the native input type for the
single-line variant (`text` default, plus `date`, `datetime-local`,
`time`, `month`, `week`, `number`, `email`, `url`, `tel`), so a date or
numeric field commits through the action system like any other —
without dropping to a raw native `<input>`.

```tsx
<ActionInput value={task.dueDate} action="task:set-due" inputType="date" />
<ActionInput value={query} action="tasks:filter" saveOn="input" placeholder="Filter…" />
```

```tsx
<ActionInput
  value={todo.title}
  action="todo:rename"
  actionData={{ todoId: todo.id }}
  saveOn="enter"
/>
```

Markdown or rich-view rendering is opt-in via the `renderView` prop to
keep the core dep-light:

```tsx
<ActionInput
  value={note.body}
  action="note:update"
  variant="multi"
  renderView={(value) => <MarkdownPreview source={value} />}
/>
```

### ActionSelect

The action-dispatching sibling of `Select`. Where `Select` binds a
`Signal<Set<T>>` and suits in-memory filter UIs, `ActionSelect` takes the
current `value` as a plain string and fires `action` with
`data-action-value` set to the chosen option — so editing a
server-backed field commits through the same event delegation as
`ActionInput` and `ActionForm`, with no synthetic signal or bridging
`effect`. A disabled `ActionSelect` renders as static text.

```tsx
<ActionSelect
  value={task.status}
  action="task:set-status"
  actionData={{ taskId: task.id }}
  options={[
    { value: 'open', label: 'Open' },
    { value: 'done', label: 'Done' },
  ]}
/>
```

### ConfirmDialog

Promise-returning confirmation. Mount `<ConfirmDialog.Host />` once near
the app root; call `confirm({ title, body, danger })` from an action
handler to prompt the user. Resolves `true` on OK, `false` on Cancel,
Escape, or backdrop click.

```tsx
import { ConfirmDialog, confirm } from '@fairfox/polly/ui';

const ACTION_REGISTRY = {
  'team:delete': async ({ data, stores }) => {
    const ok = await confirm({
      title: 'Delete team?',
      body: 'This cannot be undone.',
      danger: true,
    });
    if (!ok) return;
    await stores.data.deleteTeam(data.teamId);
  },
};

function App() {
  return (
    <>
      {/* your app */}
      <OverlayRoot />
      <ConfirmDialog.Host />
    </>
  );
}
```

### Toast

Consumes the global `errorState` signal automatically. Mount
`<Toast.Viewport />` once near the app root; `submitError` and `setError`
calls from anywhere surface as toasts. Auto-dismisses after
`autoDismissMs` (default 5s) with pause-on-hover. Severity maps to
`aria-live="polite"` for warning/info and `"assertive"` for errors.

### OverlayRoot

Portal target plus scroll-lock management. Mount once as late as
practical in your app tree; every overlay (Modal, ConfirmDialog, Toast)
portals into it. The `hasOpenOverlay()` function from
`@fairfox/polly/actions` is what drives the scroll lock, so any
overlay-like component registered with the overlay registry will behave
consistently.

## Accessibility guarantees

- Every interactive primitive has a visible focus ring whose colour
  reads from `--polly-focus-ring` (consumer may tune colour; shape and
  offset are fixed for WCAG 2.4.11 compliance).
- Every interactive element has a 44×44 minimum hit target (WCAG 2.5.8).
  Opt out via `data-polly-hit-target="none"` for dense toolbars where
  the size isn't appropriate.
- Modals trap focus inside and restore it on close.
- Toasts announce through `aria-live`.
- Reduced-motion honours `prefers-reduced-motion: reduce` by zeroing
  every `--polly-motion-*` token.
- Dialogs set `role="dialog"`, `aria-modal="true"`, and either
  `aria-labelledby` (from `Modal.Title`) or an explicit `aria-label`.

## Styling hooks

Every internal element carries a `data-polly-*` attribute for stable
selectors:

| Hook | On |
|------|----|
| `[data-polly-ui]` | Every primitive's outer element |
| `[data-polly-interactive]` | Elements with hit-target enforcement |
| `[data-polly-overlay-root]` | The portal target |
| `[data-polly-modal-content]` | Modal outer container |
| `[data-polly-modal-surface]` | Modal visible surface |
| `[data-polly-modal-backdrop]` | Modal backdrop |
| `[data-polly-action-form]` | ActionForm `<form>` element |
| `[data-polly-input]` | TextInput native input |
| `[data-polly-action-input]` | ActionInput outer element |
| `[data-polly-action-select]` | ActionSelect outer element |
| `[data-polly-cluster]` | Cluster flex-wrap container |
| `[data-polly-text]` | Text element (value is the tone) |
| `[data-polly-code]` | Code element (value is `inline` or `block`) |
| `[data-polly-toast-viewport]` | Toast portal |
| `[data-polly-toast-item]` | Individual toast |

Style overrides should hook onto these attributes rather than the
generated CSS-module class names; the module names are hashed at build
time and will change.
