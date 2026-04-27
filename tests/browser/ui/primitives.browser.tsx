/**
 * UI primitives browser test.
 *
 * Covers the critical behaviours of every @fairfox/polly/ui component:
 * mount/unmount, focus trap, Escape closes top overlay, ActionForm +
 * createForm round-trip, Toast reads errorState, Layout renders as grid,
 * TextInput in both modes.
 */

import { signal } from "@preact/signals";
import { type JSX, render } from "preact";
import {
  type ActionRegistry,
  clearError,
  createForm,
  installEventDelegation,
  resetOverlayStack,
  submitError,
} from "../../../src/actions";
import {
  ActionForm,
  Button,
  Layout,
  Modal,
  OverlayRoot,
  Surface,
  TextInput,
  Toast,
} from "../../../src/polly-ui";
import {
  cleanup,
  describe,
  done,
  expect,
  flush,
  test,
} from "../../../tools/test/src/browser/harness";

const app = document.getElementById("app") ?? document.body;

function mountHost(): HTMLElement {
  const host = document.createElement("div");
  app.appendChild(host);
  return host;
}

describe("OverlayRoot", () => {
  test("mounts a portal target with data-polly-overlay-root", async () => {
    const host = mountHost();
    render(<OverlayRoot />, host);
    await flush();
    const root = host.querySelector("[data-polly-overlay-root]");
    expect(root).toExist();
    cleanup(host);
  });
});

describe("Layout", () => {
  test("renders a grid container with configured tracks", async () => {
    const host = mountHost();
    render(
      <Layout columns="1fr 1fr" gap="var(--polly-space-lg)">
        <div data-testid="a">A</div>
        <div data-testid="b">B</div>
      </Layout>,
      host
    );
    await flush();
    const grid = host.querySelector<HTMLElement>("[data-polly-layout]");
    expect(grid).toExist();
    expect(grid!.style.getPropertyValue("--l-cols")).toBe("1fr 1fr");
    cleanup(host);
  });
});

describe("Surface", () => {
  test("plain variant sets no surface custom properties beyond defaults", async () => {
    const host = mountHost();
    render(
      <Surface>
        <div>content</div>
      </Surface>,
      host
    );
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface]");
    expect(node).toExist();
    expect(node!.getAttribute("data-polly-surface")).toBe("plain");
    expect(node!.style.getPropertyValue("--s-bg")).toBe("");
    expect(node!.style.getPropertyValue("--s-radius")).toBe("");
    cleanup(host);
  });

  test("raised variant resolves to the expected token vocabulary", async () => {
    const host = mountHost();
    render(
      <Surface variant="raised">
        <div>card</div>
      </Surface>,
      host
    );
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='raised']")!;
    expect(node).toExist();
    expect(node.style.getPropertyValue("--s-bg")).toBe("var(--polly-surface-raised)");
    expect(node.style.getPropertyValue("--s-radius")).toBe("var(--polly-radius-md)");
    expect(node.style.getPropertyValue("--s-shadow")).toBe("var(--polly-shadow-md)");
    expect(node.style.getPropertyValue("--s-border-color")).toBe("var(--polly-border)");
    expect(node.style.getPropertyValue("--s-border-width")).toBe(
      "var(--polly-border-width-default)"
    );
    cleanup(host);
  });

  test("sunken variant uses the sunken surface token", async () => {
    const host = mountHost();
    render(<Surface variant="sunken">x</Surface>, host);
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='sunken']")!;
    expect(node.style.getPropertyValue("--s-bg")).toBe("var(--polly-surface-sunken)");
    expect(node.style.getPropertyValue("--s-radius")).toBe("var(--polly-radius-md)");
    cleanup(host);
  });

  test("bubble variant carries padding and border but no background", async () => {
    const host = mountHost();
    render(<Surface variant="bubble">hi</Surface>, host);
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='bubble']")!;
    expect(node.style.getPropertyValue("--s-bg")).toBe("");
    expect(node.style.getPropertyValue("--s-p")).toBe(
      "var(--polly-space-sm) var(--polly-space-md)"
    );
    expect(node.style.getPropertyValue("--s-border-color")).toBe("var(--polly-border)");
    cleanup(host);
  });

  test("chip variant is inline with full radius", async () => {
    const host = mountHost();
    render(<Surface variant="chip">tag</Surface>, host);
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='chip']")!;
    expect(node.className).toContain("inline");
    expect(node.style.getPropertyValue("--s-radius")).toBe("var(--polly-radius-full)");
    cleanup(host);
  });

  test("callout variant has small radius and bordered padding", async () => {
    const host = mountHost();
    render(<Surface variant="callout">heads up</Surface>, host);
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='callout']")!;
    expect(node.style.getPropertyValue("--s-radius")).toBe("var(--polly-radius-sm)");
    expect(node.style.getPropertyValue("--s-p")).toBe(
      "var(--polly-space-sm) var(--polly-space-md)"
    );
    cleanup(host);
  });

  test("floating variant pins fixed with z-index and lg shadow", async () => {
    const host = mountHost();
    render(<Surface variant="floating">dock</Surface>, host);
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='floating']")!;
    expect(node.style.getPropertyValue("--s-position")).toBe("fixed");
    expect(node.style.getPropertyValue("--s-z")).toBe("9999");
    expect(node.style.getPropertyValue("--s-shadow")).toBe("var(--polly-shadow-lg)");
    expect(node.style.getPropertyValue("--s-bg")).toBe("var(--polly-surface-raised)");
    cleanup(host);
  });

  test("sticky-bar variant draws block-end border via logical class", async () => {
    const host = mountHost();
    render(<Surface variant="sticky-bar">header</Surface>, host);
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='sticky-bar']")!;
    expect(node.style.getPropertyValue("--s-position")).toBe("sticky");
    expect(node.style.getPropertyValue("--s-inset")).toBe("0 0 auto 0");
    expect(node.className).toContain("sides-block-end");
    cleanup(host);
  });

  test("explicit prop overrides variant default", async () => {
    const host = mountHost();
    render(
      <Surface variant="raised" radius="lg">
        x
      </Surface>,
      host
    );
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='raised']")!;
    expect(node.style.getPropertyValue("--s-radius")).toBe("var(--polly-radius-lg)");
    cleanup(host);
  });

  test("polymorphic as prop renders the requested element", async () => {
    const host = mountHost();
    render(
      <Surface as="section" variant="raised" aria-label="panel">
        body
      </Surface>,
      host
    );
    await flush();
    const node = host.querySelector<HTMLElement>("section[data-polly-surface]")!;
    expect(node).toExist();
    expect(node.tagName).toBe("SECTION");
    expect(node.getAttribute("aria-label")).toBe("panel");
    cleanup(host);
  });

  test("style prop merges through for per-instance polly token override", async () => {
    const host = mountHost();
    render(
      <Surface
        variant="raised"
        style={{ "--polly-surface-raised": "#fef3c7" } as JSX.CSSProperties}
      >
        x
      </Surface>,
      host
    );
    await flush();
    const node = host.querySelector<HTMLElement>("[data-polly-surface='raised']")!;
    expect(node.style.getPropertyValue("--polly-surface-raised")).toBe("#fef3c7");
    expect(node.style.getPropertyValue("--s-bg")).toBe("var(--polly-surface-raised)");
    cleanup(host);
  });
});

describe("Modal", () => {
  test("opens on signal change, closes on Escape, restores focus", async () => {
    const host = mountHost();
    resetOverlayStack();
    const open = signal(false);
    const offDelegation = installEventDelegation(() => {});

    function TestApp() {
      return (
        <div>
          <button
            id="opener"
            type="button"
            onClick={() => {
              open.value = true;
            }}
          >
            open
          </button>
          <OverlayRoot />
          <Modal.Root when={open} onClose={() => (open.value = false)}>
            <Modal.Backdrop />
            <Modal.Content>
              <Modal.Header>
                <Modal.Title>Hello</Modal.Title>
              </Modal.Header>
              <Modal.Body>
                <input id="first" />
              </Modal.Body>
              <Modal.Footer>
                <Modal.Close>Close</Modal.Close>
              </Modal.Footer>
            </Modal.Content>
          </Modal.Root>
        </div>
      );
    }

    render(<TestApp />, host);
    await flush();

    const opener = host.querySelector<HTMLButtonElement>("#opener")!;
    opener.focus();
    opener.click();
    await flush();

    const modal = document.querySelector<HTMLElement>("[data-polly-modal-content]");
    expect(modal).toExist();
    expect(modal!.getAttribute("role")).toBe("dialog");
    expect(modal!.getAttribute("aria-modal")).toBe("true");
    expect(modal!.contains(document.activeElement)).toBe(true);

    document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
    await flush();
    expect(document.querySelector("[data-polly-modal-content]")).toBeNull();
    expect(document.activeElement).toBe(opener);

    offDelegation();
    cleanup(host);
  });

  test("backdrop click closes the modal", async () => {
    const host = mountHost();
    resetOverlayStack();
    const open = signal(false);
    function TestApp() {
      return (
        <div>
          <OverlayRoot />
          <Modal.Root when={open} onClose={() => (open.value = false)}>
            <Modal.Backdrop />
            <Modal.Content>
              <Modal.Body>body</Modal.Body>
            </Modal.Content>
          </Modal.Root>
        </div>
      );
    }
    render(<TestApp />, host);
    open.value = true;
    await flush();

    const backdrop = document.querySelector<HTMLElement>("[data-polly-modal-backdrop]")!;
    backdrop.click();
    await flush();
    expect(open.value).toBe(false);
    cleanup(host);
  });
});

describe("ActionForm + createForm", () => {
  test("submit round-trip writes values through to onSubmit", async () => {
    const host = mountHost();
    resetOverlayStack();

    type Values = { name: string };
    type Stores = { received: Values[] };
    const stores: Stores = { received: [] };
    const form = createForm<Values, Stores>({
      name: "test",
      initialValues: { name: "" },
      onSubmit: async ({ values, stores: s }) => {
        s.received.push(values);
      },
    });
    form.bindStores(() => stores);

    const registry: ActionRegistry<Stores> = { ...form.actions };
    const off = installEventDelegation(async (d) => {
      const handler = registry[d.action];
      if (handler) {
        await handler({
          stores,
          event: d.event,
          element: d.element,
          data: d.data,
        });
      }
    });

    form.open();

    function TestApp() {
      return (
        <ActionForm<Values, Stores> form={form}>
          <input name="name" defaultValue="" />
          <button type="submit" id="submit-btn">
            Save
          </button>
        </ActionForm>
      );
    }
    render(<TestApp />, host);
    await flush();

    const input = host.querySelector<HTMLInputElement>("input[name=name]")!;
    input.value = "Alpha";
    const formEl = host.querySelector<HTMLFormElement>("form")!;
    formEl.requestSubmit();
    await flush(100);

    expect(stores.received).toEqual([{ name: "Alpha" }]);
    expect(form.isOpen.value).toBe(false);

    off();
    cleanup(host);
  });
});

describe("Toast", () => {
  test("renders entries from errorState and dismisses on click", async () => {
    const host = mountHost();
    clearError();
    function TestApp() {
      return (
        <div>
          <OverlayRoot />
          <Toast.Viewport autoDismissMs={100000} />
        </div>
      );
    }
    render(<TestApp />, host);
    await flush();

    submitError("x", new Error("boom"));
    await flush();

    const item = document.querySelector<HTMLElement>("[data-polly-toast-item]");
    expect(item).toExist();
    expect(item!).toHaveTextContent("boom");

    const close = document.querySelector<HTMLButtonElement>("[data-polly-toast-close]")!;
    close.click();
    await flush();
    expect(document.querySelector("[data-polly-toast-item]")).toBeNull();

    cleanup(host);
  });
});

describe("TextInput", () => {
  test("uncontrolled mode exposes name + default value for FormData", async () => {
    const host = mountHost();
    render(
      <form id="f">
        <TextInput name="handle" value="seed" />
      </form>,
      host
    );
    await flush();
    const input = host.querySelector<HTMLInputElement>("input[name=handle]")!;
    expect(input.value).toBe("seed");
    cleanup(host);
  });

  test("controlled mode writes to the signal on input", async () => {
    const host = mountHost();
    const s = signal("");
    render(<TextInput name="q" value={s} />, host);
    await flush();
    const input = host.querySelector<HTMLInputElement>("input[name=q]")!;
    input.value = "hi";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await flush();
    expect(s.value).toBe("hi");
    cleanup(host);
  });

  test("invalid prop surfaces aria-invalid and data-state", async () => {
    const host = mountHost();
    render(<TextInput name="email" invalid value="bad" />, host);
    await flush();
    const input = host.querySelector<HTMLInputElement>("input[name=email]")!;
    expect(input.getAttribute("aria-invalid")).toBe("true");
    expect(input.getAttribute("data-state")).toBe("invalid");
    cleanup(host);
  });
});

describe("Button", () => {
  // Every consumer that uses <Button> to carry additional action data
  // (data-action-tid, data-action-item-id, etc.) relies on the Button
  // rendering those attributes on the underlying button element. If
  // Button silently drops the `data-action-*` extras, clicking the
  // button fires the handler with an empty `ctx.data` and the handler
  // typically no-ops on a missing id. The bug is invisible in unit
  // tests that stub the element directly, so this test plants a real
  // Button, clicks it, and asserts the event-delegator sees every
  // attribute the JSX set.
  test("forwards data-action-* extras to the underlying element", async () => {
    let received: { action: string; data: Record<string, string> } | undefined;
    const off = installEventDelegation((d) => {
      received = { action: d.action, data: d.data };
    });

    const host = mountHost();
    render(
      <Button
        label="×"
        tier="tertiary"
        color="danger"
        data-action="task.delete"
        data-action-tid="task-17"
        data-action-label="Do laundry"
      />,
      host
    );
    await flush();

    const btn = host.querySelector<HTMLButtonElement>("button[data-action='task.delete']");
    expect(btn).toExist();
    btn?.click();
    await flush();

    expect(received?.action).toBe("task.delete");
    expect(received?.data).toEqual({ tid: "task-17", label: "Do laundry" });

    off();
    cleanup(host);
  });
});

done();
