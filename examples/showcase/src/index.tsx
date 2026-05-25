/**
 * Polly UI Showcase — visual gallery of every primitive in its
 * prop variants. Open the extension's options page to view.
 *
 * Each <Section> renders one component across its meaningful axes
 * (tier/size/state/disabled/long-label/short-label). The goal is
 * to see how a change to a component or to theme.css ripples across
 * every variant at a glance.
 */

import {
  Badge,
  Button,
  Card,
  Checkbox,
  Cluster,
  Code,
  Collapsible,
  Dropdown,
  Layout,
  Link,
  Modal,
  OverlayRoot,
  Select,
  type SelectOption,
  Skeleton,
  Surface,
  Text,
  TextInput,
  Toggle,
} from "@fairfox/polly/ui";
import { signal } from "@preact/signals";
import { type ComponentChildren, render } from "preact";

function Section({
  id,
  title,
  children,
}: {
  id: string;
  title: string;
  children: ComponentChildren;
}) {
  return (
    <section id={id} class="showcase-section" data-section={id}>
      <h2 class="showcase-section-title">{title}</h2>
      {children}
    </section>
  );
}

function Row({ label, children }: { label: string; children: ComponentChildren }) {
  return (
    <div class="showcase-row">
      <span class="showcase-row-label">{label}</span>
      {children}
    </div>
  );
}

// State for interactive components — single shared instance per
// component so the gallery shows real behaviour, not a freeze frame.
const singleSelect = signal(new Set<string>(["banana"]));
const multiSelectShort = signal(new Set<string>(["apple", "banana"]));
const multiSelectLong = signal(
  new Set<string>(["apple", "banana", "cherry", "date", "elderberry"])
);
const checkboxValue = signal(true);
const textShort = signal("hello");
const textLong = signal(
  "a much longer value that demonstrates how the input behaves with overflowing content"
);
const dropdownOpen = signal(false);
const dropdownOpenStyled = signal(false);
const modalOpen = signal(false);

type ThemeMode = "light" | "dark" | "system";
type Direction = "ltr" | "rtl";

const themeMode = signal<ThemeMode>(
  (localStorage.getItem("showcase-theme") as ThemeMode | null) ?? "system",
);
const direction = signal<Direction>(
  (localStorage.getItem("showcase-dir") as Direction | null) ?? "ltr",
);

function applyTheme(mode: ThemeMode): void {
  const root = document.documentElement;
  if (mode === "system") root.removeAttribute("data-polly-theme");
  else root.setAttribute("data-polly-theme", mode);
  localStorage.setItem("showcase-theme", mode);
}
function applyDir(dir: Direction): void {
  document.documentElement.setAttribute("dir", dir);
  localStorage.setItem("showcase-dir", dir);
}
applyTheme(themeMode.value);
applyDir(direction.value);

function Toolbar() {
  return (
    <div class="showcase-toolbar">
      <span class="showcase-row-label">theme</span>
      {(["light", "dark", "system"] as const).map((mode) => (
        <button
          key={mode}
          type="button"
          class={`showcase-chip ${themeMode.value === mode ? "showcase-chip-active" : ""}`}
          onClick={() => {
            themeMode.value = mode;
            applyTheme(mode);
          }}
        >
          {mode}
        </button>
      ))}
      <span class="showcase-row-label" style={{ marginLeft: "var(--polly-space-lg)" }}>
        dir
      </span>
      {(["ltr", "rtl"] as const).map((dir) => (
        <button
          key={dir}
          type="button"
          class={`showcase-chip ${direction.value === dir ? "showcase-chip-active" : ""}`}
          onClick={() => {
            direction.value = dir;
            applyDir(dir);
          }}
        >
          {dir}
        </button>
      ))}
    </div>
  );
}

const fruits: SelectOption<string>[] = [
  { value: "apple", label: "Apple" },
  { value: "banana", label: "Banana" },
  { value: "cherry", label: "Cherry" },
  { value: "date", label: "Date" },
  { value: "elderberry", label: "Elderberry — a deliberately long option label" },
];

function Showcase() {
  return (
    <div class="showcase-root">
      <Text size="xl" weight="bold">
        Polly UI Showcase
      </Text>
      <Text tone="muted">
        Visual gallery of every UI primitive across its prop variants. Use for local development and
        as a smoke test for theme/component changes.
      </Text>
      <Toolbar />

      <Section id="text" title="Text">
        <Row label="sizes">
          <Text size="xs">xs</Text>
          <Text size="sm">sm</Text>
          <Text size="md">md</Text>
          <Text size="lg">lg</Text>
          <Text size="xl">xl</Text>
        </Row>
        <Row label="weights">
          <Text weight="normal">normal</Text>
          <Text weight="medium">medium</Text>
          <Text weight="bold">bold</Text>
        </Row>
        <Row label="tones">
          <Text tone="default">default</Text>
          <Text tone="muted">muted</Text>
          <Text tone="success">success</Text>
          <Text tone="warning">warning</Text>
          <Text tone="danger">danger</Text>
        </Row>
      </Section>

      <Section id="badge" title="Badge">
        <Row label="variants">
          <Badge>default</Badge>
          <Badge variant="info">info</Badge>
          <Badge variant="success">success</Badge>
          <Badge variant="warning">warning</Badge>
          <Badge variant="danger">danger</Badge>
        </Row>
      </Section>

      <Section id="button" title="Button">
        <Row label="tiers">
          <Button tier="primary" label="Primary" />
          <Button tier="secondary" label="Secondary" />
          <Button tier="tertiary" label="Tertiary" />
        </Row>
        <Row label="colors (primary)">
          <Button tier="primary" color="info" label="Info" />
          <Button tier="primary" color="success" label="Success" />
          <Button tier="primary" color="warning" label="Warning" />
          <Button tier="primary" color="danger" label="Danger" />
        </Row>
        <Row label="sizes">
          <Button size="small" label="Small" />
          <Button size="normal" label="Normal" />
          <Button size="large" label="Large" />
        </Row>
        <Row label="states">
          <Button label="Enabled" />
          <Button disabled label="Disabled" />
          <Button circle label="•" aria-label="Circle" />
        </Row>
        <Row label="bounded">
          <Button
            label="A deliberately long button label that should ellipsis-truncate at the max-width cap"
            bounded
          />
          <Button label="Unbounded — long label expands as far as it likes" />
        </Row>
      </Section>

      <Section id="link" title="Link">
        <Row label="default">
          <Link href="#">Inline link</Link>
        </Row>
      </Section>

      <Section id="code" title="Code">
        <Row label="inline">
          <Text>
            Use <Code>$sharedState</Code> to declare cross-context signals.
          </Text>
        </Row>
      </Section>

      <Section id="checkbox-toggle" title="Checkbox / Toggle">
        <Row label="checkbox">
          <Checkbox label="Bound to signal" checked={checkboxValue} />
          <Checkbox label="Default checked" defaultChecked />
          <Checkbox label="Disabled" disabled />
        </Row>
        <Row label="toggle">
          <Toggle label="Off" />
          <Toggle label="On" checked />
          <Toggle label="Disabled" disabled />
        </Row>
      </Section>

      <Section id="textinput" title="TextInput">
        <Row label="short">
          <label htmlFor="ti-short" class="showcase-field-label">
            <span class="showcase-field-name">Short</span>
            <TextInput name="short" id="ti-short" value={textShort} placeholder="Type…" />
          </label>
        </Row>
        <Row label="long">
          <label htmlFor="ti-long" class="showcase-field-label showcase-wide">
            <span class="showcase-field-name">Long</span>
            <TextInput name="long" id="ti-long" value={textLong} />
          </label>
        </Row>
        <Row label="states">
          <label htmlFor="ti-placeholder" class="showcase-field-label">
            <span class="showcase-field-name">Placeholder</span>
            <TextInput name="placeholder" id="ti-placeholder" placeholder="placeholder only" />
          </label>
          <label htmlFor="ti-invalid" class="showcase-field-label">
            <span class="showcase-field-name">Invalid</span>
            <TextInput name="invalid" id="ti-invalid" value="invalid" invalid />
          </label>
          <label htmlFor="ti-disabled" class="showcase-field-label">
            <span class="showcase-field-name">Disabled</span>
            <TextInput name="disabled-ti" id="ti-disabled" value="disabled" disabled />
          </label>
          <label htmlFor="ti-readonly" class="showcase-field-label">
            <span class="showcase-field-name">Read only</span>
            <TextInput name="readonly" id="ti-readonly" value="readonly" readOnly />
          </label>
        </Row>
        <Row label="textarea">
          <label htmlFor="ti-textarea" class="showcase-field-label showcase-wide">
            <span class="showcase-field-name">Multi-line</span>
            <TextInput name="textarea" id="ti-textarea" rows={3} placeholder="multi-line" />
          </label>
        </Row>
      </Section>

      <Section id="select-single" title="Select (single)">
        <Row label="default">
          <Select options={fruits} selected={singleSelect} placeholder="Pick a fruit" />
        </Row>
        <Row label="wide opt-in">
          <Select options={fruits} selected={singleSelect} wide />
        </Row>
        <Row label="disabled">
          <Select options={fruits} selected={singleSelect} disabled />
        </Row>
      </Section>

      <Section id="select-multi" title="Select (multi)">
        <Row label="few chosen">
          <Select options={fruits} selected={multiSelectShort} multiSelect wide />
        </Row>
        <Row label="many chosen (collapses to 'N selected')">
          <Select options={fruits} selected={multiSelectLong} multiSelect wide />
        </Row>
      </Section>

      <Section id="dropdown" title="Dropdown">
        <Row label="raw default">
          <Dropdown isOpen={dropdownOpen} trigger="Open menu">
            <div style={{ padding: "var(--polly-space-md)", minWidth: "12rem" }}>
              <Text>Arbitrary menu content.</Text>
            </div>
          </Dropdown>
        </Row>
        <Row label="styled via triggerClassName">
          <Dropdown
            isOpen={dropdownOpenStyled}
            trigger="Open menu"
            triggerClassName="showcase-dropdown-trigger"
          >
            <div style={{ padding: "var(--polly-space-md)", minWidth: "12rem" }}>
              <Text>
                The default trigger is intentionally minimal so consumers can supply their own
                button styling (Select does this internally).
              </Text>
            </div>
          </Dropdown>
        </Row>
      </Section>

      <Section id="surface" title="Surface">
        <Layout columns="repeat(3, 1fr)" gap="var(--polly-space-md)">
          <Surface variant="plain" padding="var(--polly-space-md)">
            <Layout rows="auto auto" gap="var(--polly-space-xs)">
              <Text weight="bold">plain</Text>
              <Text tone="muted" size="sm">
                surface preset
              </Text>
            </Layout>
          </Surface>
          <Surface variant="sunken" padding="var(--polly-space-md)">
            <Layout rows="auto auto" gap="var(--polly-space-xs)">
              <Text weight="bold">sunken</Text>
              <Text tone="muted" size="sm">
                surface preset
              </Text>
            </Layout>
          </Surface>
          <Surface variant="raised" padding="var(--polly-space-md)">
            <Layout rows="auto auto" gap="var(--polly-space-xs)">
              <Text weight="bold">raised</Text>
              <Text tone="muted" size="sm">
                surface preset
              </Text>
            </Layout>
          </Surface>
        </Layout>
      </Section>

      <Section id="modal" title="Modal">
        <Row label="open">
          <button
            type="button"
            class="showcase-chip"
            onClick={() => {
              modalOpen.value = true;
            }}
          >
            Open modal
          </button>
        </Row>
      </Section>

      <Section id="card" title="Card">
        <Card.Root>
          <Card.Header>
            <Text weight="bold">Card header</Text>
          </Card.Header>
          <Card.Body>
            <Text>
              Card body — composes Surface slots. Use for grouped content where header/body/footer
              have distinct affordances.
            </Text>
          </Card.Body>
          <Card.Footer>
            <Cluster gap="var(--polly-space-sm)">
              <Button tier="tertiary" label="Cancel" />
              <Button tier="primary" label="Confirm" />
            </Cluster>
          </Card.Footer>
        </Card.Root>
      </Section>

      <Section id="cluster-layout" title="Cluster / Layout">
        <Row label="cluster">
          <Cluster gap="var(--polly-space-sm)">
            <Badge variant="info">a</Badge>
            <Badge variant="success">b</Badge>
            <Badge variant="warning">c</Badge>
            <Badge variant="danger">d</Badge>
          </Cluster>
        </Row>
        <Row label="layout 3-col">
          <div class="showcase-wide">
            <Layout columns="repeat(3, 1fr)" gap="var(--polly-space-sm)">
              <Surface variant="sunken" padding="var(--polly-space-sm)">
                <Text>col 1</Text>
              </Surface>
              <Surface variant="sunken" padding="var(--polly-space-sm)">
                <Text>col 2</Text>
              </Surface>
              <Surface variant="sunken" padding="var(--polly-space-sm)">
                <Text>col 3</Text>
              </Surface>
            </Layout>
          </div>
        </Row>
      </Section>

      <Section id="collapsible" title="Collapsible">
        <Collapsible summary="Click to expand">
          <Text>Hidden content revealed when the disclosure opens.</Text>
        </Collapsible>
        <Collapsible summary="Default open" defaultOpen>
          <Text>This one starts open.</Text>
        </Collapsible>
      </Section>

      <Section id="skeleton" title="Skeleton">
        <Row label="text">
          <div class="showcase-wide">
            <Skeleton variant="text" />
            <Skeleton variant="text" width="60%" />
            <Skeleton variant="text" width="80%" />
          </div>
        </Row>
        <Row label="rect / circle">
          <Skeleton variant="rect" width={120} height={80} />
          <Skeleton variant="circle" width={48} height={48} />
        </Row>
      </Section>

      <OverlayRoot />
      <Modal.Root
        when={modalOpen}
        onClose={() => {
          modalOpen.value = false;
        }}
        aria-label="Example modal"
      >
        <Modal.Backdrop />
        <Modal.Content>
          <Modal.Header>
            <Modal.Title>Example modal</Modal.Title>
            <Modal.Close>×</Modal.Close>
          </Modal.Header>
          <Modal.Body>
            <Text>
              Modal mounts into the OverlayRoot portal, traps focus, and closes on Escape or
              backdrop click. The header has a built-in close affordance.
            </Text>
          </Modal.Body>
          <Modal.Footer>
            <Cluster gap="var(--polly-space-sm)">
              <Modal.Close>Cancel</Modal.Close>
            </Cluster>
          </Modal.Footer>
        </Modal.Content>
      </Modal.Root>
    </div>
  );
}

const root = document.getElementById("root");
if (root) render(<Showcase />, root);
