/**
 * Dropdown — trigger button + popover menu using the native Popover API.
 *
 * A shown popover is promoted to the browser's top layer, where CSS
 * positioning resolves against the viewport rather than the `.dropdown`
 * wrapper — so the menu cannot be placed with `position: absolute`
 * alone. Instead it is pinned with `position: fixed` and coordinates
 * measured from the trigger; see `positionMenu` below (issue #128).
 *
 * The menu element gets `popover="auto"` and a unique `data-overlay-id`.
 * `closeTopOverlay()` from @fairfox/polly/actions finds the topmost
 * `[data-overlay-id]` element and dispatches `overlay:close` — the
 * Dropdown listens for that event and mirrors it onto the `isOpen`
 * signal. In single-select mode, clicking the menu closes it; in
 * multi-select mode, the menu stays open so the consumer can pick
 * several items.
 */

import { type Signal, useSignalEffect } from "@preact/signals";
import type { ComponentChildren, JSX } from "preact";
import { useEffect, useRef } from "preact/hooks";
import classes from "./Dropdown.module.css";
import { Layout } from "./Layout.tsx";

export type DropdownProps = {
  isOpen: Signal<boolean>;
  trigger: ComponentChildren;
  children: ComponentChildren;
  align?: "left" | "right";
  multiSelect?: boolean;
  className?: string;
  /**
   * Class applied to the trigger <button> in place of Dropdown's own
   * default. Lets a composing component (Select, ActionSelect) style
   * the single interactive element directly, with no styled node
   * nested inside the button. The trigger also carries a
   * `data-open="true|false"` attribute mirroring `isOpen`, so the
   * class can style open-state affordances (e.g. a rotating caret).
   */
  triggerClassName?: string;
  /** Disables the trigger <button>. */
  triggerDisabled?: boolean;
  id?: string;
};

let dropdownCounter = 0;

/** Gap in px the menu leaves between itself and the trigger. */
const MENU_GAP = 4;
/** Minimum gap in px the menu keeps from every viewport edge. */
const VIEWPORT_PADDING = 8;

export function Dropdown(props: DropdownProps): JSX.Element {
  const {
    isOpen,
    trigger,
    children,
    align = "left",
    multiSelect = false,
    className,
    triggerClassName,
    triggerDisabled = false,
    id,
  } = props;

  const menuRef = useRef<HTMLDivElement>(null);
  const triggerRef = useRef<HTMLButtonElement>(null);
  const idRef = useRef(`polly-dropdown-${++dropdownCounter}`);
  const popoverId = idRef.current;

  useEffect(() => {
    triggerRef.current?.setAttribute("popovertarget", popoverId);
  }, [popoverId]);

  useEffect(() => {
    const menu = menuRef.current;
    if (!menu) return;
    const onOverlayClose = (e: Event): void => {
      if (e instanceof CustomEvent && e.detail?.id === popoverId) {
        isOpen.value = false;
      }
    };
    menu.addEventListener("overlay:close", onOverlayClose);
    return () => {
      menu.removeEventListener("overlay:close", onOverlayClose);
    };
  }, [popoverId, isOpen]);

  useEffect(() => {
    const menu = menuRef.current;
    const trigger = triggerRef.current;
    if (!menu || !trigger) return;

    // Pin the top-layer menu to its trigger with viewport coordinates.
    // Run from `beforetoggle` this happens synchronously before the
    // popover paints, so the menu is correct on its first frame — no
    // flash. Run from scroll/resize it keeps the menu pinned.
    const positionMenu = (): void => {
      const t = trigger.getBoundingClientRect();

      // A not-yet-shown popover is `display: none` and has no box to
      // measure. Force layout for the duration of the (synchronous)
      // read, then restore — nothing paints in between. Clearing the
      // inline max-height first measures the menu's natural size.
      const prevDisplay = menu.style.display;
      menu.style.maxHeight = "";
      menu.style.display = "block";
      const menuWidth = menu.offsetWidth;
      const menuHeight = menu.offsetHeight;
      menu.style.display = prevDisplay;

      const viewportWidth = document.documentElement.clientWidth;
      const viewportHeight = document.documentElement.clientHeight;

      // Horizontal: align left edges (right edges when align="right"),
      // then clamp so the menu never overflows a viewport edge.
      let left = align === "right" ? t.right - menuWidth : t.left;
      const maxLeft = Math.max(VIEWPORT_PADDING, viewportWidth - menuWidth - VIEWPORT_PADDING);
      left = Math.min(Math.max(left, VIEWPORT_PADDING), maxLeft);

      // Vertical: below the trigger by default; flip above when that
      // leaves more room. Cap the height to the space available so the
      // menu always stays on-screen.
      const spaceBelow = viewportHeight - t.bottom - MENU_GAP - VIEWPORT_PADDING;
      const spaceAbove = t.top - MENU_GAP - VIEWPORT_PADDING;
      let top: number;
      if (menuHeight <= spaceBelow || spaceBelow >= spaceAbove) {
        top = t.bottom + MENU_GAP;
        if (menuHeight > spaceBelow) {
          menu.style.maxHeight = `${Math.max(spaceBelow, 0)}px`;
        }
      } else {
        const available = Math.max(spaceAbove, 0);
        menu.style.maxHeight = `${available}px`;
        top = t.top - MENU_GAP - Math.min(menuHeight, available);
      }

      menu.style.position = "fixed";
      menu.style.margin = "0";
      menu.style.left = `${left}px`;
      menu.style.top = `${top}px`;
    };

    const onBeforeToggle = (e: Event): void => {
      if ((e as Event & { newState?: string }).newState === "open") {
        positionMenu();
      }
    };
    const onReposition = (): void => {
      if (menu.matches(":popover-open")) positionMenu();
    };

    menu.addEventListener("beforetoggle", onBeforeToggle);
    window.addEventListener("scroll", onReposition, true);
    window.addEventListener("resize", onReposition);
    return () => {
      menu.removeEventListener("beforetoggle", onBeforeToggle);
      window.removeEventListener("scroll", onReposition, true);
      window.removeEventListener("resize", onReposition);
    };
  }, [align]);

  useSignalEffect(() => {
    const menu = menuRef.current;
    if (!menu) return;
    if (isOpen.value && !menu.matches(":popover-open")) {
      menu.showPopover();
    } else if (!isOpen.value && menu.matches(":popover-open")) {
      menu.hidePopover();
    }
  });

  const handleToggle = (e: Event): void => {
    if ("newState" in e) {
      isOpen.value = (e as unknown as { newState: string }).newState === "open";
    }
  };

  const handleMenuClick = (): void => {
    if (!multiSelect) {
      isOpen.value = false;
    }
  };

  const handleKeyDown = (e: KeyboardEvent): void => {
    if (e.key === "Escape") {
      isOpen.value = false;
    }
  };

  const parts = [classes["dropdown"] ?? ""];
  if (className) parts.push(className);

  return (
    <div id={id} class={parts.filter(Boolean).join(" ")} data-polly-ui data-polly-dropdown>
      <button
        ref={triggerRef}
        type="button"
        class={triggerClassName ?? classes["trigger"] ?? ""}
        disabled={triggerDisabled}
        data-open={isOpen.value ? "true" : "false"}
      >
        {trigger}
      </button>
      <div
        ref={menuRef}
        id={popoverId}
        role="listbox"
        class={classes["menu"] ?? ""}
        data-align={align}
        popover="auto"
        data-overlay-id={popoverId}
        onToggle={handleToggle}
        onClick={handleMenuClick}
        onKeyDown={handleKeyDown}
      >
        <Layout rows="auto" gap="0">
          {children}
        </Layout>
      </div>
    </div>
  );
}
