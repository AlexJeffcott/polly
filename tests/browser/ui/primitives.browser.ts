/**
 * UI primitives browser test.
 *
 * Covers the critical behaviours of every @fairfox/polly/ui component:
 * mount/unmount, focus trap, Escape closes top overlay, ActionForm +
 * createForm round-trip, Toast reads errorState, Layout renders as grid,
 * TextInput in both modes.
 */

import { signal } from "@preact/signals";
import { h, render } from "preact";
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
  Layout,
  Modal,
  OverlayRoot,
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
    render(h(OverlayRoot, null), host);
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
      h(
        Layout,
        { columns: "1fr 1fr", gap: "var(--polly-space-lg)" },
        h("div", { "data-testid": "a" }, "A"),
        h("div", { "data-testid": "b" }, "B"),
      ),
      host,
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

    const App = () =>
      h(
        "div",
        null,
        h("button", {
          id: "opener",
          onClick: () => {
            open.value = true;
          },
        }, "open"),
        h(OverlayRoot, null),
        h(
          Modal.Root,
          { when: open, onClose: () => (open.value = false) },
          h(Modal.Backdrop, null),
          h(
            Modal.Content,
            null,
            h(
              Modal.Header,
              null,
              h(Modal.Title, null, "Hello"),
            ),
            h(Modal.Body, null, h("input", { id: "first" })),
            h(
              Modal.Footer,
              null,
              h(Modal.Close, null, "Close"),
            ),
          ),
        ),
      );

    render(h(App, null), host);
    await flush();

    const opener = host.querySelector<HTMLButtonElement>("#opener")!;
    opener.focus();
    opener.click();
    await flush();

    const modal = document.querySelector<HTMLElement>(
      "[data-polly-modal-content]",
    );
    expect(modal).toExist();
    expect(modal!.getAttribute("role")).toBe("dialog");
    expect(modal!.getAttribute("aria-modal")).toBe("true");

    // Focus should have moved inside the modal.
    expect(modal!.contains(document.activeElement)).toBe(true);

    // Escape closes.
    document.dispatchEvent(
      new KeyboardEvent("keydown", { key: "Escape", bubbles: true }),
    );
    await flush();
    expect(
      document.querySelector("[data-polly-modal-content]"),
    ).toBeNull();
    // Focus restored to the opener.
    expect(document.activeElement).toBe(opener);

    offDelegation();
    cleanup(host);
  });

  test("backdrop click closes the modal", async () => {
    const host = mountHost();
    resetOverlayStack();
    const open = signal(false);
    const App = () =>
      h(
        "div",
        null,
        h(OverlayRoot, null),
        h(
          Modal.Root,
          { when: open, onClose: () => (open.value = false) },
          h(Modal.Backdrop, null),
          h(Modal.Content, null, h(Modal.Body, null, "body")),
        ),
      );
    render(h(App, null), host);
    open.value = true;
    await flush();

    const backdrop = document.querySelector<HTMLElement>(
      "[data-polly-modal-backdrop]",
    )!;
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

    const App = () =>
      h(
        ActionForm<Values, Stores>,
        { form },
        h("input", { name: "name", defaultValue: "" }),
        h("button", { type: "submit", id: "submit-btn" }, "Save"),
      );
    render(h(App, null), host);
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
    const App = () => h("div", null, h(OverlayRoot, null), h(Toast.Viewport, { autoDismissMs: 100000 }));
    render(h(App, null), host);
    await flush();

    submitError("x", new Error("boom"));
    await flush();

    const item = document.querySelector<HTMLElement>(
      "[data-polly-toast-item]",
    );
    expect(item).toExist();
    expect(item!).toHaveTextContent("boom");

    const close = document.querySelector<HTMLButtonElement>(
      "[data-polly-toast-close]",
    )!;
    close.click();
    await flush();
    expect(
      document.querySelector("[data-polly-toast-item]"),
    ).toBeNull();

    cleanup(host);
  });
});

describe("TextInput", () => {
  test("uncontrolled mode exposes name + default value for FormData", async () => {
    const host = mountHost();
    render(
      h(
        "form",
        { id: "f" },
        h(TextInput, { name: "handle", value: "seed" }),
      ),
      host,
    );
    await flush();
    const input = host.querySelector<HTMLInputElement>("input[name=handle]")!;
    expect(input.value).toBe("seed");
    cleanup(host);
  });

  test("controlled mode writes to the signal on input", async () => {
    const host = mountHost();
    const s = signal("");
    render(h(TextInput, { name: "q", value: s }), host);
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
    render(
      h(TextInput, { name: "email", invalid: true, value: "bad" }),
      host,
    );
    await flush();
    const input = host.querySelector<HTMLInputElement>("input[name=email]")!;
    expect(input.getAttribute("aria-invalid")).toBe("true");
    expect(input.getAttribute("data-state")).toBe("invalid");
    cleanup(host);
  });
});

done();
