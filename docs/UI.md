# UI primitives

`@fairfox/polly/ui` provides eight compound components that sit on top of
the action-registry runtime. The split of responsibility is deliberate:
Polly owns accessibility and structure; consumers own visual values.

## Import

```ts
import {
  Layout, Modal, ActionForm, TextInput, ActionInput,
  ConfirmDialog, Toast, OverlayRoot,
} from '@fairfox/polly/ui';

import '@fairfox/polly/ui/styles.css';      // structural + a11y — keep it
import '@fairfox/polly/ui/theme.css';       // default tokens — override or replace
import '@fairfox/polly/ui/components.css';  // per-component styles — keep it
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
`explicit`). Commit fires the configured action with a synthetic hidden
element carrying `data-action-value`, so the existing delegation picks
it up. View and edit modes share padding, border width, font, and
line-height so toggling between them causes zero layout shift.

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
| `[data-polly-toast-viewport]` | Toast portal |
| `[data-polly-toast-item]` | Individual toast |

Style overrides should hook onto these attributes rather than the
generated CSS-module class names; the module names are hashed at build
time and will change.
