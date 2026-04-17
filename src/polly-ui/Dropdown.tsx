/**
 * Dropdown — trigger button + popover menu using the native Popover API.
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
  id?: string;
};

let dropdownCounter = 0;

export function Dropdown(props: DropdownProps): JSX.Element {
  const { isOpen, trigger, children, align = "left", multiSelect = false, className, id } = props;

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

  const menuParts = [classes["menu"] ?? ""];
  if (align === "right") menuParts.push(classes["alignRight"] ?? "");

  return (
    <div id={id} class={parts.filter(Boolean).join(" ")} data-polly-ui data-polly-dropdown>
      <button ref={triggerRef} type="button" class={classes["trigger"]}>
        {trigger}
      </button>
      <div
        ref={menuRef}
        id={popoverId}
        role="listbox"
        class={menuParts.filter(Boolean).join(" ")}
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
