/**
 * Regression test for polly#177 — Modal.Root's overlay effect re-running on
 * every render.
 *
 * `onClose` sat in the effect's dependency array. Consumers pass an inline
 * closure, so the prop had a new identity on every render and the effect tore
 * down and re-installed each time: `popOverlay` + `pushOverlay` wrote the
 * module-level `stack` signal twice per render, and the focus trap moved focus
 * twice. Because the signal write re-rendered its subscribers, and each render
 * produced the next closure, the cycle fed itself — a runaway render loop that
 * pinned the browser's main thread at 100% CPU and stopped every timer in the
 * page.
 *
 * The observable the tests below use is the identity of the array behind
 * `overlayStack()`. Every push and pop assigns a fresh array, so an unchanged
 * reference across a re-render is direct proof the effect did not re-run.
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

const { h, render } = await import("preact");
const { act } = await import("preact/test-utils");
const { Modal } = await import("../../src/polly-ui/Modal.tsx");
const { OverlayRoot } = await import("../../src/polly-ui/OverlayRoot.tsx");
const { closeTopOverlay, overlayStack, resetOverlayStack } = await import(
  "../../src/actions/overlay.ts"
);

const hosts: HTMLElement[] = [];

/** Render the overlay root and an open modal into a fresh document body. */
function mountHost(): HTMLElement {
  const host = document.createElement("div");
  document.body.appendChild(host);
  hosts.push(host);
  return host;
}

/** One render pass with a fresh `onClose` closure, as a consumer writes it. */
async function renderModal(host: HTMLElement, onClose: () => void): Promise<void> {
  await act(async () => {
    render(
      h("div", null, [
        h(OverlayRoot, {}),
        // Modal's parts declare `children` as a required prop, and preact's
        // `h` overloads want it in the props object rather than as trailing
        // arguments, so every part below passes it explicitly.
        h(Modal.Root, {
          when: true,
          onClose,
          "aria-label": "test dialog",
          children: h(Modal.Content, { children: h(Modal.Close, { children: "Close" }) }),
        }),
      ]),
      host
    );
  });
}

// Unmount rather than clearing innerHTML. OverlayRoot holds a live signal
// effect for the scroll lock; detaching its DOM leaves that effect subscribed
// to the module-level overlay stack, and the next test file to push an
// overlay would run it against a document that no longer exists.
afterEach(async () => {
  for (const host of hosts.splice(0)) {
    await act(async () => {
      render(null, host);
    });
    host.remove();
  }
  resetOverlayStack();
});

describe("Modal.Root overlay effect (polly#177)", () => {
  test("registers exactly one overlay entry when opened", async () => {
    const host = mountHost();
    await renderModal(host, () => {});

    expect(overlayStack()).toHaveLength(1);
  });

  test("does not re-run when only the onClose identity changes", async () => {
    const host = mountHost();
    await renderModal(host, () => {});
    const afterMount = overlayStack();
    expect(afterMount).toHaveLength(1);

    // A second render pass with a brand-new closure — the identity change that
    // used to tear the overlay down and re-install it.
    await renderModal(host, () => {});

    expect(overlayStack()).toBe(afterMount);
    expect(overlayStack()).toHaveLength(1);
  });

  test("survives repeated renders without growing or churning the stack", async () => {
    const host = mountHost();
    await renderModal(host, () => {});
    const afterMount = overlayStack();

    for (let i = 0; i < 10; i++) {
      await renderModal(host, () => {});
    }

    expect(overlayStack()).toBe(afterMount);
    expect(overlayStack()).toHaveLength(1);
  });

  test("the registered entry calls the newest onClose, not the one from mount", async () => {
    const host = mountHost();
    const called: string[] = [];
    await renderModal(host, () => called.push("first"));
    await renderModal(host, () => called.push("second"));

    closeTopOverlay();

    expect(called).toEqual(["second"]);
  });

  test("closing the modal pops its entry", async () => {
    const host = mountHost();
    await renderModal(host, () => {});
    expect(overlayStack()).toHaveLength(1);

    await act(async () => {
      render(
        h("div", null, [h(OverlayRoot, {}), h(Modal.Root, { when: false, children: "hidden" })]),
        host
      );
    });

    expect(overlayStack()).toHaveLength(0);
  });
});
