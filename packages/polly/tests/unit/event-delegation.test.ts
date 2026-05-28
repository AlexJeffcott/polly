/**
 * Regression tests for polly#140 — clicking the trigger of the last
 * `[data-overlay-id]` popover in the DOM closed it and immediately reopened it.
 *
 * Two interacting causes, both guarded here:
 *
 *  1. `closeTopOverlay()` resolved "top" by DOM order alone, so it dispatched
 *     `overlay:close` on the last `[data-overlay-id]` element even when that
 *     element was closed. The fix scopes the query to open overlays
 *     (`:popover-open` / `dialog[open]`).
 *
 *  2. The document `mousedown` handler fired on every trigger click, racing the
 *     native popover toggle into a close-then-reopen. The fix ignores mousedowns
 *     originating on a `button[popovertarget]` invoker.
 *
 * happy-dom has no popover API (`showPopover` is absent, `:popover-open` matches
 * nothing), which is exactly the pre-fix trap: a closed overlay must no longer
 * be treated as "top". The open-overlay positive path is exercised with a
 * `<dialog open>`, which happy-dom does support.
 */

import { afterAll, beforeAll, beforeEach, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";

beforeAll(() => {
  GlobalRegistrator.register();
});

afterAll(async () => {
  await GlobalRegistrator.unregister();
});

// Imported after the DOM globals exist.
const { closeTopOverlay, installEventDelegation } = await import("@/actions/event-delegation");

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("closeTopOverlay (polly#140)", () => {
  test("does not close an overlay that is merely last in the DOM but not open", () => {
    const overlay = document.createElement("div");
    overlay.setAttribute("data-overlay-id", "last-but-closed");
    document.body.appendChild(overlay);

    let closes = 0;
    overlay.addEventListener("overlay:close", () => {
      closes++;
    });

    closeTopOverlay();

    // Pre-fix this dispatched on the last DOM element regardless of open state,
    // which is what reopened the trigger.
    expect(closes).toBe(0);
  });

  test("closes an actually-open overlay (<dialog open>)", () => {
    const dialog = document.createElement("dialog");
    dialog.setAttribute("data-overlay-id", "menu");
    dialog.setAttribute("open", "");
    document.body.appendChild(dialog);

    const closedIds: string[] = [];
    dialog.addEventListener("overlay:close", (e) => {
      closedIds.push((e as CustomEvent).detail.id);
    });

    closeTopOverlay();

    expect(closedIds).toEqual(["menu"]);
  });
});

describe("installEventDelegation mousedown light-dismiss (polly#140)", () => {
  test("ignores a mousedown originating on a popover invoker button", () => {
    const trigger = document.createElement("button");
    trigger.setAttribute("popovertarget", "menu");
    document.body.appendChild(trigger);

    let outside = 0;
    const cleanup = installEventDelegation(() => {}, {
      onOutsideOverlayClick: () => {
        outside++;
      },
    });

    trigger.dispatchEvent(new MouseEvent("mousedown", { bubbles: true }));

    // The native popover API owns invoker clicks; the redundant close used to
    // race it and reopen the popover.
    expect(outside).toBe(0);
    cleanup();
  });

  test("still dismisses on a mousedown outside any overlay or invoker", () => {
    const elsewhere = document.createElement("div");
    document.body.appendChild(elsewhere);

    let outside = 0;
    const cleanup = installEventDelegation(() => {}, {
      onOutsideOverlayClick: () => {
        outside++;
      },
    });

    elsewhere.dispatchEvent(new MouseEvent("mousedown", { bubbles: true }));

    expect(outside).toBe(1);
    cleanup();
  });
});
