/**
 * UI primitives browser test.
 *
 * Covers the critical behaviours of every @fairfox/polly/ui component:
 * mount/unmount, focus trap, Escape closes top overlay, ActionForm +
 * createForm round-trip, Toast reads errorState, Layout renders as grid,
 * TextInput in both modes.
 */

import { signal } from "@preact/signals";
import { render } from "preact";
import {
  type ActionRegistry,
  clearError,
  createForm,
  installEventDelegation,
  resetOverlayStack,
  submitError,
} from "../../../src/actions";
import { ActionForm, Layout, Modal, OverlayRoot, TextInput, Toast } from "../../../src/polly-ui";
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

done();
