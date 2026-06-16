/**
 * The gallery catalogue — one section per polly-ui primitive, each rendering
 * the configurations worth seeing. Adapted from eal's showcase (which consumes
 * this very library), repointed at the local source so the gallery renders the
 * primitives exactly as they ship.
 *
 * Every section carries a `component` naming the polly-ui export it covers;
 * registry-coverage.ts asserts that every component in registry.generated.ts
 * has a section here, so a new primitive can't land without a specimen.
 */

import type { ComponentChildren, JSX } from "preact";
import {
  ActionForm,
  ActionInput,
  ActionSelect,
  Badge,
  Button,
  Card,
  Checkbox,
  Cluster,
  Code,
  Collapsible,
  Dropdown,
  FileInput,
  Html,
  Layout,
  Link,
  Modal,
  Output,
  Select,
  Skeleton,
  Surface,
  Tabs,
  Text,
  TextInput,
  Toggle,
} from "../../../src/polly-ui";
import {
  $galleryChecked,
  $galleryCommitted,
  $galleryDropdownOpen,
  $galleryFileName,
  $galleryModalOpen,
  $gallerySelectClearable,
  $gallerySelectMulti,
  $gallerySelectSingle,
  $galleryTab,
  $galleryText,
  galleryForm,
} from "./stores.ts";

/**
 * One catalogued example: a stage holding live component(s) and a caption
 * naming the configuration on show. `wide` spans every grid column for
 * specimens that need the room (layouts, forms, cards).
 */
function Specimen(props: { caption: string; wide?: boolean; children: ComponentChildren }) {
  return (
    <Surface
      variant="sunken"
      radius="md"
      border="default"
      padding="var(--polly-space-md)"
      className={props.wide ? "gallery-specimen gallery-specimen--wide" : "gallery-specimen"}
    >
      <Layout gap="var(--polly-space-sm)">
        <div class="gallery-stage">{props.children}</div>
        <Text size="xs" tone="muted" className="gallery-code">
          {props.caption}
        </Text>
      </Layout>
    </Surface>
  );
}

/** A neutral filler block for the layout specimens. */
function Box(props: { children: ComponentChildren }) {
  return (
    <Surface variant="raised" radius="sm" border="default" padding="var(--polly-space-sm)">
      <Text size="sm">{props.children}</Text>
    </Surface>
  );
}

const STAR: JSX.Element = (
  <span aria-hidden="true" class="gallery-icon">
    ★
  </span>
);

export interface GallerySection {
  /** Anchor id for the in-page nav. */
  id: string;
  /** Display heading. */
  title: string;
  /** The polly-ui export this section covers (matched against the registry). */
  component: string;
  /** One-line description. */
  summary: string;
  render: () => JSX.Element;
}

export const GALLERY_SECTIONS: readonly GallerySection[] = [
  {
    id: "badge",
    title: "Badge",
    component: "Badge",
    summary: "Small inline status chip. One variant per semantic tone.",
    render: () => (
      <>
        {(["default", "info", "success", "warning", "danger"] as const).map((v) => (
          <Specimen key={v} caption={`variant="${v}"`}>
            <Badge variant={v}>{v}</Badge>
          </Specimen>
        ))}
      </>
    ),
  },
  {
    id: "button",
    title: "Button",
    component: "Button",
    summary: "Interactive control. Tier sets importance, color overlays meaning, size sets scale.",
    render: () => (
      <>
        <Specimen caption="tier: primary / secondary / tertiary">
          <Button tier="primary" label="Primary" />
          <Button tier="secondary" label="Secondary" />
          <Button tier="tertiary" label="Tertiary" />
        </Specimen>
        <Specimen caption="color: default / info / success / warning / danger">
          <Button color="default" label="Default" />
          <Button color="info" label="Info" />
          <Button color="success" label="Success" />
          <Button color="warning" label="Warning" />
          <Button color="danger" label="Danger" />
        </Specimen>
        <Specimen caption="size: small / normal / large">
          <Button size="small" label="Small" />
          <Button size="normal" label="Normal" />
          <Button size="large" label="Large" />
        </Specimen>
        <Specimen caption="disabled">
          <Button label="Disabled" disabled />
        </Specimen>
        <Specimen caption="icon + label">
          <Button icon={STAR} label="With icon" />
        </Specimen>
        <Specimen caption="circle (icon-only needs aria-label)">
          <Button circle aria-label="Star" label={STAR} />
        </Specimen>
        <Specimen caption="href — renders an <a>">
          <Button href="#button" tier="secondary" label="Link button" />
        </Specimen>
        <Specimen caption="fullWidth" wide>
          <Button fullWidth tier="primary" label="Full-width button" />
        </Specimen>
      </>
    ),
  },
  {
    id: "text",
    title: "Text",
    component: "Text",
    summary: "Typographic primitive — tone, size, weight, italic, strikethrough, and leading.",
    render: () => (
      <>
        <Specimen caption="tone: default / muted / danger / warning / success">
          <Text tone="default">Default</Text>
          <Text tone="muted">Muted</Text>
          <Text tone="danger">Danger</Text>
          <Text tone="warning">Warning</Text>
          <Text tone="success">Success</Text>
        </Specimen>
        <Specimen caption="size: xs / sm / md / lg / xl">
          {(["xs", "sm", "md", "lg", "xl"] as const).map((s) => (
            <Text key={s} size={s}>
              {s}
            </Text>
          ))}
        </Specimen>
        <Specimen caption="weight: normal / medium / bold">
          <Text weight="normal">Normal</Text>
          <Text weight="medium">Medium</Text>
          <Text weight="bold">Bold</Text>
        </Specimen>
        <Specimen caption="italic / strikethrough">
          <Text italic>Italic emphasis</Text>
          <Text strikethrough>Struck through</Text>
        </Specimen>
        <Specimen caption='leading="loose" — multi-line body copy' wide>
          <Text as="p" leading="loose">
            A paragraph rendered with loose leading. Polly's Text primitive backs every span,
            paragraph, label, and caption so consumers never reach for a raw style attribute to set
            tone, size, weight, or line height.
          </Text>
        </Specimen>
      </>
    ),
  },
  {
    id: "code",
    title: "Code",
    component: "Code",
    summary: "Monospace code — inline by default, or a wrapped block.",
    render: () => (
      <>
        <Specimen caption="inline">
          <Text>
            Run <Code>polly gallery</Code> to open this page.
          </Text>
        </Specimen>
        <Specimen caption="block" wide>
          <Code block>{'const gallery = {\n  served: "by polly",\n};'}</Code>
        </Specimen>
      </>
    ),
  },
  {
    id: "link",
    title: "Link",
    component: "Link",
    summary: "Anchor primitive — underline by default, with external, subtle, and download modes.",
    render: () => (
      <>
        <Specimen caption="default">
          <Link href="#link">In-page link</Link>
        </Specimen>
        <Specimen caption="external — new tab, rel=noopener">
          <Link href="https://example.com" external>
            External link
          </Link>
        </Specimen>
        <Specimen caption="subtle — underline on hover only">
          <Link href="#link" subtle>
            Subtle link
          </Link>
        </Specimen>
        <Specimen caption="download">
          <Link href="data:text/plain,gallery" download="gallery.txt">
            Download link
          </Link>
        </Specimen>
      </>
    ),
  },
  {
    id: "surface",
    title: "Surface",
    component: "Surface",
    summary: "Owns visual chrome — background, border, radius, shadow, positioning.",
    render: () => (
      <>
        {(["plain", "raised", "sunken", "bubble", "chip", "callout"] as const).map((v) => (
          <Specimen key={v} caption={`variant="${v}"`}>
            <Surface variant={v} padding="var(--polly-space-md)">
              <Text size="sm">{v}</Text>
            </Surface>
          </Specimen>
        ))}
        <Specimen caption='variant: "floating" / "sticky-bar" pin to the viewport — omitted here'>
          <Text size="xs" tone="muted">
            Positional variants are previewed in context, not in a grid cell.
          </Text>
        </Specimen>
        <Specimen caption="radius: none / sm / md / lg / full">
          {(["none", "sm", "md", "lg", "full"] as const).map((r) => (
            <Surface
              key={r}
              variant="raised"
              border="default"
              radius={r}
              padding="var(--polly-space-sm)"
            >
              <Text size="xs">{r}</Text>
            </Surface>
          ))}
        </Specimen>
        <Specimen caption="border: none / default / strong">
          {(["none", "default", "strong"] as const).map((b) => (
            <Surface key={b} border={b} radius="md" padding="var(--polly-space-sm)">
              <Text size="xs">{b}</Text>
            </Surface>
          ))}
        </Specimen>
        <Specimen caption="shadow: sm / md / lg">
          {(["sm", "md", "lg"] as const).map((s) => (
            <Surface
              key={s}
              variant="raised"
              shadow={s}
              radius="md"
              padding="var(--polly-space-sm)"
            >
              <Text size="xs">{s}</Text>
            </Surface>
          ))}
        </Specimen>
      </>
    ),
  },
  {
    id: "card",
    title: "Card",
    component: "Card",
    summary: "Compound of Surfaces — a raised Root wrapping Header, Body, and Footer slots.",
    render: () => (
      <Specimen caption="Card.Root > Header / Body / Footer" wide>
        <Card.Root padding="0">
          <Card.Header padding="var(--polly-space-md)">
            <Text weight="bold">Card header</Text>
          </Card.Header>
          <Card.Body padding="var(--polly-space-md)">
            <Text>
              The body slot carries the main content. Each slot accepts the full SurfaceProps, so it
              can be retinted or repadded without reaching past the primitive.
            </Text>
          </Card.Body>
          <Card.Footer padding="var(--polly-space-md)">
            <Button size="small" tier="primary" label="Footer action" />
          </Card.Footer>
        </Card.Root>
      </Specimen>
    ),
  },
  {
    id: "skeleton",
    title: "Skeleton",
    component: "Skeleton",
    summary: "Shimmering placeholder for loading states. Animation honours reduced-motion.",
    render: () => (
      <>
        {(["text", "rect", "circle"] as const).map((v) => (
          <Specimen key={v} caption={`variant="${v}"`}>
            <Skeleton variant={v} />
          </Specimen>
        ))}
        <Specimen caption="custom width + height">
          <Skeleton variant="rect" width="100%" height={64} />
        </Specimen>
      </>
    ),
  },
  {
    id: "output",
    title: "Output",
    component: "Output",
    summary:
      "Monospace output region for command results or logs — wraps, or scrolls horizontally.",
    render: () => (
      <>
        <Specimen caption="default — wraps" wide>
          <Output>polly gallery → serving at http://localhost:4321</Output>
        </Specimen>
        <Specimen caption="scroll — single long line scrolls instead of wrapping" wide>
          <Output scroll>
            {
              "$ polly gallery --build ./dist/gallery   # one long line that scrolls horizontally rather than wrapping onto the next row"
            }
          </Output>
        </Specimen>
      </>
    ),
  },
  {
    id: "html",
    title: "Html",
    component: "Html",
    summary: "Renders a trusted HTML string. The caller owns sanitisation — never pass user input.",
    render: () => (
      <Specimen caption="html={trusted string}" wide>
        <Html html="<strong>Bold</strong>, <em>italic</em>, and a <code>code span</code> from a trusted markup string." />
      </Specimen>
    ),
  },
  {
    id: "collapsible",
    title: "Collapsible",
    component: "Collapsible",
    summary: "Native <details>/<summary> disclosure — keyboard and screen-reader behaviour free.",
    render: () => (
      <>
        <Specimen caption="closed by default" wide>
          <Collapsible summary="Show more detail">
            <Text>This content is revealed when the disclosure is opened.</Text>
          </Collapsible>
        </Specimen>
        <Specimen caption="defaultOpen" wide>
          <Collapsible summary="Open from the start" defaultOpen>
            <Text>This collapsible renders expanded on first paint.</Text>
          </Collapsible>
        </Specimen>
        <Specimen caption="editable field in the summary — Space/Enter no longer collapse it" wide>
          <Collapsible
            summary={
              <TextInput name="gallery-collapsible-summary" placeholder="Type a space here…" />
            }
          >
            <Text>The header guard cancels the disclosure toggle for text-entry fields.</Text>
          </Collapsible>
        </Specimen>
      </>
    ),
  },
  {
    id: "layout",
    title: "Layout",
    component: "Layout",
    summary:
      "The grid primitive. Props map to CSS custom properties — no hand-written flex or grid.",
    render: () => (
      <>
        <Specimen caption='columns="1fr 1fr 1fr"' wide>
          <Layout columns="1fr 1fr 1fr" gap="var(--polly-space-sm)">
            <Box>1fr</Box>
            <Box>1fr</Box>
            <Box>1fr</Box>
          </Layout>
        </Specimen>
        <Specimen caption='columns="auto 1fr auto"' wide>
          <Layout columns="auto 1fr auto" gap="var(--polly-space-sm)" alignItems="center">
            <Box>auto</Box>
            <Box>1fr</Box>
            <Box>auto</Box>
          </Layout>
        </Specimen>
        <Specimen caption="stackOnMobile — collapses to one column ≤640px" wide>
          <Layout columns="1fr 1fr" gap="var(--polly-space-sm)" stackOnMobile>
            <Box>Side by side, then stacked</Box>
            <Box>Side by side, then stacked</Box>
          </Layout>
        </Specimen>
      </>
    ),
  },
  {
    id: "cluster",
    title: "Cluster",
    component: "Cluster",
    summary:
      "Wrapping row of variable-width items — chips, tags, button groups. Reflows as space runs out.",
    render: () => (
      <Specimen caption="gap — items wrap onto new rows" wide>
        <Cluster gap="var(--polly-space-xs)">
          {["Groceries", "Errands", "Home", "Garden", "Finance", "Travel", "Health", "Admin"].map(
            (tag) => (
              <Badge key={tag} variant="info">
                {tag}
              </Badge>
            )
          )}
        </Cluster>
      </Specimen>
    ),
  },
  {
    id: "tabs",
    title: "Tabs",
    component: "Tabs",
    summary: "Horizontal nav with an active-tab accent. Dispatches an action per tab.",
    render: () => (
      <Specimen caption="interactive — one tab disabled" wide>
        <Tabs
          tabs={[
            { id: "overview", label: "Overview" },
            { id: "activity", label: "Activity" },
            { id: "settings", label: "Settings" },
            { id: "archived", label: "Archived", disabled: true },
          ]}
          activeTab={$galleryTab.value}
          action="gallery:set-tab"
          aria-label="Gallery tabs"
        />
      </Specimen>
    ),
  },
  {
    id: "checkbox",
    title: "Checkbox",
    component: "Checkbox",
    summary: "Native checkbox in a label. A plain boolean is controlled; a Signal binds itself.",
    render: () => (
      <>
        <Specimen caption="unchecked">
          <Checkbox label="Unchecked" checked={false} />
        </Specimen>
        <Specimen caption="checked">
          <Checkbox label="Checked" checked={true} />
        </Specimen>
        <Specimen caption="disabled">
          <Checkbox label="Disabled" checked={true} disabled />
        </Specimen>
        <Specimen caption="checked={signal} — click to toggle">
          <Checkbox label="Bound to a signal" checked={$galleryChecked} />
        </Specimen>
      </>
    ),
  },
  {
    id: "toggle",
    title: "Toggle",
    component: "Toggle",
    summary: "Switch-role checkbox. Passive — the caller drives the checked state.",
    render: () => (
      <>
        <Specimen caption="off">
          <Toggle label="Off" checked={false} />
        </Specimen>
        <Specimen caption="on">
          <Toggle label="On" checked={true} />
        </Specimen>
        <Specimen caption="disabled">
          <Toggle label="Disabled" checked={true} disabled />
        </Specimen>
      </>
    ),
  },
  {
    id: "text-input",
    title: "TextInput",
    component: "TextInput",
    summary:
      "Signal-friendly native input. A plain string is uncontrolled; a Signal is controlled. " +
      "inputType picks the native keyboard and validation; error renders a linked message.",
    render: () => (
      <>
        <Specimen caption='variant="single" with placeholder'>
          <TextInput name="demo-single" placeholder="Type here…" />
        </Specimen>
        <Specimen caption='variant="multi"'>
          <TextInput name="demo-multi" variant="multi" rows={3} placeholder="Multiple lines…" />
        </Specimen>
        <Specimen caption='inputType="email"'>
          <TextInput name="demo-email" inputType="email" placeholder="ada@example.com" />
        </Specimen>
        <Specimen caption='inputType="number" with min/max/step'>
          <TextInput name="demo-number" inputType="number" min={0} max={10} step={1} value="5" />
        </Specimen>
        <Specimen caption="error — linked message, marks invalid">
          <TextInput name="demo-error" value="not-an-email" error="Enter a valid email address." />
        </Specimen>
        <Specimen caption="invalid">
          <TextInput name="demo-invalid" value="not-an-email" invalid />
        </Specimen>
        <Specimen caption="disabled">
          <TextInput name="demo-disabled" value="Disabled" disabled />
        </Specimen>
        <Specimen caption="readOnly">
          <TextInput name="demo-readonly" value="Read only" readOnly />
        </Specimen>
        <Specimen caption="value={signal} — controlled">
          <TextInput name="demo-controlled" value={$galleryText} />
        </Specimen>
      </>
    ),
  },
  {
    id: "select",
    title: "Select",
    component: "Select",
    summary:
      "Dropdown of options bound to a Signal<Set>. Single replaces, multi toggles. " +
      'clearable prepends an "Any …" row so an optional filter has a path back to unset.',
    render: () => (
      <>
        <Specimen caption="single-select">
          <Select
            label="Pick one"
            options={[
              { value: "comet", label: "Comet" },
              { value: "nebula", label: "Nebula" },
              { value: "quasar", label: "Quasar" },
            ]}
            selected={$gallerySelectSingle}
          />
        </Specimen>
        <Specimen caption="clearable — single-select with an “Any …” row">
          <Select
            label="Filter by"
            placeholder="Any object"
            clearable
            options={[
              { value: "comet", label: "Comet" },
              { value: "nebula", label: "Nebula" },
              { value: "quasar", label: "Quasar" },
            ]}
            selected={$gallerySelectClearable}
          />
        </Specimen>
        <Specimen caption="multiSelect">
          <Select
            label="Pick several"
            multiSelect
            options={[
              { value: "comet", label: "Comet" },
              { value: "nebula", label: "Nebula" },
              { value: "quasar", label: "Quasar" },
            ]}
            selected={$gallerySelectMulti}
          />
        </Specimen>
      </>
    ),
  },
  {
    id: "file-input",
    title: "FileInput",
    component: "FileInput",
    summary: "Styled wrapper over a native file picker. Hands the chosen FileList to onFiles.",
    render: () => (
      <>
        <Specimen caption="onFiles — pick a file">
          <FileInput
            label="Choose file"
            onFiles={(files) => {
              $galleryFileName.value = files[0]?.name ?? "—";
            }}
          />
        </Specimen>
        <Specimen caption="accept + multiple">
          <FileInput
            label="Choose images"
            accept="image/*"
            multiple
            onFiles={(files) => {
              $galleryFileName.value = files[0]?.name ?? "—";
            }}
          />
        </Specimen>
        <Specimen caption="disabled">
          <FileInput
            label="Disabled"
            disabled
            onFiles={() => {
              /* disabled — never invoked */
            }}
          />
        </Specimen>
        <Specimen caption="last picked file" wide>
          <Text tone="muted">
            Last picked: <Code>{$galleryFileName.value}</Code>
          </Text>
        </Specimen>
      </>
    ),
  },
  {
    id: "dropdown",
    title: "Dropdown",
    component: "Dropdown",
    summary:
      "Low-level trigger + popover plumbing. The primitive itself has no chrome — " +
      "consumers (Select, ActionSelect) wrap it with the styled trigger and caret.",
    render: () => (
      <Specimen caption="trigger dressed via triggerClassName + data-open">
        <Dropdown
          isOpen={$galleryDropdownOpen}
          triggerClassName="gallery-dropdown-trigger"
          trigger={
            <>
              <span>Open menu</span>
              <span class="gallery-dropdown-caret" aria-hidden="true" />
            </>
          }
        >
          <Layout gap="var(--polly-space-xs)" padding="var(--polly-space-xs)">
            <Text>First item</Text>
            <Text>Second item</Text>
            <Text>Third item</Text>
          </Layout>
        </Dropdown>
      </Specimen>
    ),
  },
  {
    id: "action-input",
    title: "ActionInput",
    component: "ActionInput",
    summary: "Dual-mode view/edit field. Click to edit; commit dispatches an action.",
    render: () => (
      <>
        <Specimen caption='saveOn="blur"'>
          <ActionInput
            value="Click to edit, commits on blur"
            action="gallery:commit"
            saveOn="blur"
            ariaLabel="Blur-commit demo"
          />
        </Specimen>
        <Specimen caption='saveOn="enter"'>
          <ActionInput
            value="Edit and press Enter"
            action="gallery:commit"
            saveOn="enter"
            ariaLabel="Enter-commit demo"
          />
        </Specimen>
        <Specimen caption='inputType="date"'>
          <ActionInput
            value="2026-05-22"
            action="gallery:commit"
            inputType="date"
            saveOn="blur"
            ariaLabel="Date demo"
          />
        </Specimen>
        <Specimen caption='variant="multi"'>
          <ActionInput
            value="A longer, multi-line value"
            action="gallery:commit"
            variant="multi"
            saveOn="blur"
            ariaLabel="Multi-line demo"
          />
        </Specimen>
        <Specimen caption="last committed value" wide>
          <Text tone="muted">
            Last committed: <Code>{$galleryCommitted.value}</Code>
          </Text>
        </Specimen>
      </>
    ),
  },
  {
    id: "action-select",
    title: "ActionSelect",
    component: "ActionSelect",
    summary: "Single-select that commits a plain string value through the action system.",
    render: () => (
      <>
        <Specimen caption="commits via action">
          <ActionSelect
            label="Priority"
            value="medium"
            options={[
              { value: "low", label: "Low" },
              { value: "medium", label: "Medium" },
              { value: "high", label: "High" },
            ]}
            action="gallery:commit"
          />
        </Specimen>
        <Specimen caption="disabled — renders as static text">
          <ActionSelect
            label="Priority"
            value="high"
            options={[
              { value: "low", label: "Low" },
              { value: "medium", label: "Medium" },
              { value: "high", label: "High" },
            ]}
            action="gallery:commit"
            disabled
          />
        </Specimen>
      </>
    ),
  },
  {
    id: "action-form",
    title: "ActionForm",
    component: "ActionForm",
    summary: "Wraps a native form with the action pattern — submit dispatches the form handler.",
    render: () => (
      <Specimen caption="form with TextInput fields + a submit Button" wide>
        <ActionForm form={galleryForm} aria-label="Gallery demo form">
          <Layout gap="var(--polly-space-sm)">
            <Text as="label" size="sm" tone="muted" htmlFor="gallery-form-name">
              Full name
            </Text>
            <TextInput id="gallery-form-name" name="fullName" placeholder="Ada Lovelace" />
            <Text as="label" size="sm" tone="muted" htmlFor="gallery-form-email">
              Email
            </Text>
            <TextInput id="gallery-form-email" name="email" placeholder="ada@example.com" />
            <Button type="submit" tier="primary" color="info" label="Submit" />
          </Layout>
        </ActionForm>
      </Specimen>
    ),
  },
  {
    id: "modal",
    title: "Modal",
    component: "Modal",
    summary: "Compound dialog — focus trap, Escape handling, portal, scroll lock.",
    render: () => (
      <Specimen caption="opens a portalled dialog">
        <Button tier="primary" data-action="gallery:modal-open" label="Open modal" />
        <Modal.Root
          when={$galleryModalOpen}
          onClose={() => {
            $galleryModalOpen.value = false;
          }}
          aria-label="Demo modal"
        >
          <Modal.Backdrop />
          <Modal.Content>
            <Modal.Header>
              <Modal.Title>Modal title</Modal.Title>
            </Modal.Header>
            <Modal.Body>
              <Text>
                Focus is trapped inside the dialog, Escape closes it, the backdrop click closes it,
                and the body scroll is locked while it is open.
              </Text>
            </Modal.Body>
            <Modal.Footer>
              <Modal.Close>
                <Button tier="primary" label="Done" />
              </Modal.Close>
            </Modal.Footer>
          </Modal.Content>
        </Modal.Root>
      </Specimen>
    ),
  },
  {
    id: "confirm-dialog",
    title: "ConfirmDialog",
    component: "ConfirmDialog",
    summary: "Promise-returning confirmation. confirm() resolves true or false.",
    render: () => (
      <>
        <Specimen caption="confirm() — standard">
          <Button tier="secondary" data-action="gallery:confirm" label="Confirm an action" />
        </Specimen>
        <Specimen caption="confirm({ danger: true })">
          <Button
            tier="secondary"
            color="danger"
            data-action="gallery:confirm"
            data-action-danger="true"
            label="Confirm a deletion"
          />
        </Specimen>
      </>
    ),
  },
  {
    id: "toast",
    title: "Toast",
    component: "Toast",
    summary: "Renders the global errorState signal. Severity sets the aria-live politeness.",
    render: () => (
      <Specimen caption="push a toast at each severity" wide>
        <Cluster gap="var(--polly-space-sm)">
          <Button
            tier="secondary"
            color="info"
            data-action="gallery:toast"
            data-action-severity="info"
            label="Info toast"
          />
          <Button
            tier="secondary"
            color="warning"
            data-action="gallery:toast"
            data-action-severity="warning"
            label="Warning toast"
          />
          <Button
            tier="secondary"
            color="danger"
            data-action="gallery:toast"
            data-action-severity="error"
            label="Error toast"
          />
        </Cluster>
      </Specimen>
    ),
  },
  {
    id: "overlay-root",
    title: "OverlayRoot",
    component: "OverlayRoot",
    summary:
      "Infrastructure, not a visual control. Mount it once near the app root; Modal, Toast, and " +
      "ConfirmDialog portal into it. The gallery shell already mounts one — this section documents it.",
    render: () => (
      <Specimen caption="mounted once at the app root" wide>
        <Text>
          <Code>{"<OverlayRoot />"}</Code> renders the portal target the overlay primitives need.
          Without it, the Modal / Toast / ConfirmDialog specimens above would have nowhere to
          render. It draws nothing itself; the gallery shell mounts the single live instance.
        </Text>
      </Specimen>
    ),
  },
];
