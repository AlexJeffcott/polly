/**
 * Modal's compound parts and the focus trap behind them.
 *
 * Both were untested until polly#177 put them under a coverage floor: the
 * focus trap turned out to be the hottest frame in a runaway render loop, and
 * nothing in the suite exercised its Tab handling or its focus restore. The
 * parts are checked through the accessibility wiring consumers rely on —
 * `aria-labelledby`/`aria-describedby` pointing at the real Title and Body —
 * rather than through their markup alone.
 */

import "./helpers/css-module-keys.ts";
import { afterAll, afterEach, beforeAll, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";

beforeAll(() => {
  GlobalRegistrator.register();
});

afterAll(async () => {
  await GlobalRegistrator.unregister();
});

import type { ComponentChildren } from "preact";

const { h, render } = await import("preact");
const { act } = await import("preact/test-utils");
const { Modal } = await import("../../src/polly-ui/Modal.tsx");
const { OverlayRoot } = await import("../../src/polly-ui/OverlayRoot.tsx");
const { installFocusTrap } = await import("../../src/polly-ui/internal/focus-trap.ts");
const { resetOverlayStack } = await import("../../src/actions/overlay.ts");

const hosts: HTMLElement[] = [];

function mountHost(): HTMLElement {
  const host = document.createElement("div");
  document.body.appendChild(host);
  hosts.push(host);
  return host;
}

/**
 * Render a full modal with the given body, and return the dialog element.
 *
 * Modal's parts declare `children` as a required prop, and preact's `h`
 * overloads want it in the props object rather than as trailing arguments, so
 * every part in this file passes it explicitly.
 */
async function openModal(
  children: ComponentChildren,
  props: Record<string, unknown> = {}
): Promise<HTMLElement> {
  const host = mountHost();
  await act(async () => {
    render(
      h("div", null, [h(OverlayRoot, {}), h(Modal.Root, { when: true, ...props, children })]),
      host
    );
  });
  const dialog = document.querySelector("[data-polly-modal-content]");
  if (!(dialog instanceof HTMLElement)) throw new Error("the modal did not open");
  return dialog;
}

afterEach(async () => {
  for (const host of hosts.splice(0)) {
    await act(async () => {
      render(null, host);
    });
    host.remove();
  }
  document.body.innerHTML = "";
  resetOverlayStack();
});

describe("Modal parts", () => {
  test("Title and Body are wired to the dialog's aria attributes", async () => {
    const dialog = await openModal(
      h(Modal.Content, {
        children: [
          h(Modal.Header, { children: h(Modal.Title, { children: "Delete file" }) }),
          h(Modal.Body, { children: "This cannot be undone." }),
        ],
      })
    );

    const titleId = dialog.getAttribute("aria-labelledby");
    const descId = dialog.getAttribute("aria-describedby");
    expect(titleId).toBeTruthy();
    expect(document.getElementById(titleId ?? "")?.textContent).toBe("Delete file");
    expect(document.getElementById(descId ?? "")?.textContent).toBe("This cannot be undone.");
  });

  test("an explicit aria-label replaces the Title reference", async () => {
    const dialog = await openModal(
      h(Modal.Content, { children: h(Modal.Title, { children: "Ignored" }) }),
      { "aria-label": "Settings" }
    );

    expect(dialog.getAttribute("aria-label")).toBe("Settings");
    expect(dialog.getAttribute("aria-labelledby")).toBeNull();
  });

  test("the dialog carries the modal role and open state", async () => {
    const dialog = await openModal(h(Modal.Content, { children: "body" }), {
      "aria-label": "x",
    });

    expect(dialog.getAttribute("role")).toBe("dialog");
    expect(dialog.getAttribute("aria-modal")).toBe("true");
    expect(dialog.getAttribute("data-state")).toBe("open");
    expect(dialog.getAttribute("data-overlay-id")).toBeTruthy();
  });

  test("Content merges a caller's className with its own surface class", async () => {
    await openModal(h(Modal.Content, { className: "app-sheet", children: "body" }), {
      "aria-label": "x",
    });

    const surface = document.querySelector("[data-polly-modal-surface]");
    expect(surface?.className).toContain("app-sheet");
    expect(surface?.className.split(" ").length).toBeGreaterThan(1);
  });

  test("Header and Footer render their own hooks", async () => {
    await openModal(
      h(Modal.Content, {
        children: [h(Modal.Header, { children: "head" }), h(Modal.Footer, { children: "foot" })],
      }),
      { "aria-label": "x" }
    );

    expect(document.querySelector("[data-polly-modal-header]")?.textContent).toBe("head");
    expect(document.querySelector("[data-polly-modal-footer]")?.textContent).toBe("foot");
  });

  test("the backdrop closes the modal", async () => {
    let closed = 0;
    await openModal([h(Modal.Backdrop, {}), h(Modal.Content, { children: "body" })], {
      "aria-label": "x",
      onClose: () => {
        closed += 1;
      },
    });

    const backdrop = document.querySelector("[data-polly-modal-backdrop]");
    expect(backdrop?.getAttribute("aria-hidden")).toBe("true");
    await act(async () => {
      backdrop?.dispatchEvent(new MouseEvent("click", { bubbles: true }));
    });

    expect(closed).toBe(1);
  });

  test("Close calls onClose when it has no action", async () => {
    let closed = 0;
    await openModal(h(Modal.Content, { children: h(Modal.Close, { children: "Done" }) }), {
      "aria-label": "x",
      onClose: () => {
        closed += 1;
      },
    });

    const button = document.querySelector("[data-polly-modal-close]");
    expect(button?.getAttribute("data-action")).toBeNull();
    await act(async () => {
      button?.dispatchEvent(new MouseEvent("click", { bubbles: true }));
    });

    expect(closed).toBe(1);
  });

  test("Close with an action defers to the action system instead", async () => {
    let closed = 0;
    await openModal(
      h(Modal.Content, { children: h(Modal.Close, { action: "sheet:close", children: "Done" }) }),
      {
        "aria-label": "x",
        onClose: () => {
          closed += 1;
        },
      }
    );

    const button = document.querySelector("[data-polly-modal-close]");
    expect(button?.getAttribute("data-action")).toBe("sheet:close");
    await act(async () => {
      button?.dispatchEvent(new MouseEvent("click", { bubbles: true }));
    });

    expect(closed).toBe(0);
  });

  test("a closed Root renders nothing", async () => {
    const host = mountHost();
    await act(async () => {
      render(
        h("div", null, [
          h(OverlayRoot, {}),
          h(Modal.Root, { when: false, children: h(Modal.Content, { children: "body" }) }),
        ]),
        host
      );
    });

    expect(document.querySelector("[data-polly-modal-content]")).toBeNull();
  });

  test("a sub-component outside Root fails loudly", () => {
    const host = mountHost();

    expect(() => render(h(Modal.Title, { children: "orphan" }), host)).toThrow(
      "Modal sub-components must render inside <Modal.Root>"
    );
  });
});

describe("installFocusTrap", () => {
  /** A root with three buttons, attached to the document. */
  function trapRoot(): { root: HTMLElement; buttons: HTMLButtonElement[] } {
    const root = document.createElement("div");
    const buttons = ["one", "two", "three"].map((label) => {
      const button = document.createElement("button");
      button.textContent = label;
      root.appendChild(button);
      return button;
    });
    document.body.appendChild(root);
    hosts.push(root);
    return { root, buttons };
  }

  function tab(shiftKey = false): KeyboardEvent {
    const event = new KeyboardEvent("keydown", {
      key: "Tab",
      shiftKey,
      bubbles: true,
      cancelable: true,
    });
    document.dispatchEvent(event);
    return event;
  }

  test("moves focus to the first focusable element", () => {
    const { buttons } = trapRoot();
    const release = installFocusTrap(buttons[0]?.parentElement as HTMLElement);

    expect(document.activeElement).toBe(buttons[0] ?? null);
    release();
  });

  test("leaves focus alone when it is already inside", () => {
    const { root, buttons } = trapRoot();
    buttons[2]?.focus();

    const release = installFocusTrap(root);

    expect(document.activeElement).toBe(buttons[2] ?? null);
    release();
  });

  test("focuses the root itself when it holds nothing focusable", () => {
    const root = document.createElement("div");
    root.tabIndex = -1;
    root.textContent = "no controls";
    document.body.appendChild(root);
    hosts.push(root);

    const release = installFocusTrap(root);

    expect(document.activeElement).toBe(root);
    release();
  });

  test("Tab from the last element wraps to the first", () => {
    const { root, buttons } = trapRoot();
    const release = installFocusTrap(root);
    buttons[2]?.focus();

    const event = tab();

    expect(event.defaultPrevented).toBe(true);
    expect(document.activeElement).toBe(buttons[0] ?? null);
    release();
  });

  test("Tab elsewhere in the list is left to the browser", () => {
    const { root, buttons } = trapRoot();
    const release = installFocusTrap(root);
    buttons[0]?.focus();

    const event = tab();

    expect(event.defaultPrevented).toBe(false);
    release();
  });

  test("Shift+Tab from the first element wraps to the last", () => {
    const { root, buttons } = trapRoot();
    const release = installFocusTrap(root);
    buttons[0]?.focus();

    const event = tab(true);

    expect(event.defaultPrevented).toBe(true);
    expect(document.activeElement).toBe(buttons[2] ?? null);
    release();
  });

  test("Shift+Tab from outside the root pulls focus back to the last element", () => {
    const outside = document.createElement("button");
    document.body.appendChild(outside);
    hosts.push(outside);
    const { root, buttons } = trapRoot();
    const release = installFocusTrap(root);
    outside.focus();

    const event = tab(true);

    expect(event.defaultPrevented).toBe(true);
    expect(document.activeElement).toBe(buttons[2] ?? null);
    release();
  });

  test("a disabled or aria-hidden control is not a tab stop", () => {
    const { root, buttons } = trapRoot();
    buttons[0]?.setAttribute("disabled", "");
    buttons[1]?.setAttribute("aria-hidden", "true");
    const release = installFocusTrap(root);

    // Only the third button remains focusable, so it is both first and last.
    expect(document.activeElement).toBe(buttons[2] ?? null);
    const event = tab();
    expect(event.defaultPrevented).toBe(true);
    expect(document.activeElement).toBe(buttons[2] ?? null);
    release();
  });

  test("Tab is swallowed when nothing inside can take focus", () => {
    const root = document.createElement("div");
    root.textContent = "nothing here";
    document.body.appendChild(root);
    hosts.push(root);
    const release = installFocusTrap(root);

    const event = tab();

    expect(event.defaultPrevented).toBe(true);
    release();
  });

  test("keys other than Tab pass straight through", () => {
    const { root } = trapRoot();
    const release = installFocusTrap(root);

    const event = new KeyboardEvent("keydown", { key: "a", bubbles: true, cancelable: true });
    document.dispatchEvent(event);

    expect(event.defaultPrevented).toBe(false);
    release();
  });

  test("release restores focus to the element that had it and stops trapping", () => {
    const opener = document.createElement("button");
    document.body.appendChild(opener);
    hosts.push(opener);
    opener.focus();
    const { root, buttons } = trapRoot();

    const release = installFocusTrap(root);
    expect(document.activeElement).toBe(buttons[0] ?? null);

    release();

    expect(document.activeElement).toBe(opener);
    // The keydown listener is gone: a Tab that would have wrapped does nothing.
    buttons[2]?.focus();
    expect(tab().defaultPrevented).toBe(false);
  });

  test("release does not restore focus to an element that has left the document", () => {
    const opener = document.createElement("button");
    document.body.appendChild(opener);
    opener.focus();
    const { root } = trapRoot();
    const release = installFocusTrap(root);
    opener.remove();

    expect(() => release()).not.toThrow();
  });
});
