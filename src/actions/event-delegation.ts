/**
 * Event delegation core.
 *
 * One document listener dispatches `data-action` events to typed handlers.
 * Walks up the DOM with `closest('[data-action]')`, parses `data-action-*`
 * attributes into a camelCase object, and hands the dispatch to the caller.
 *
 * Forms are skipped on click — a `<form data-action="...">` responds to
 * submit only, so clicks on form children don't bubble into its action.
 * Escape closes the topmost overlay by calling the overlay registry.
 * Enter/Space on non-interactive elements with `data-action` fire the
 * action (Space is prevented to stop page scroll). Click outside any
 * `[data-overlay-id]` element also pops the top overlay.
 */

import { closeTopOverlay as closeTopRegistryOverlay } from "./overlay.ts";

/** Elements that natively fire click on Enter/Space. */
export const INTERACTIVE_TAGS = new Set(["BUTTON", "A", "INPUT", "SELECT", "TEXTAREA"]);

/** Event types that may trigger a data-action dispatch. */
export const ACTION_EVENT_TYPES = new Set(["click", "submit", "change", "input"]);

/** Parsed action dispatch — what the runtime resolves before invoking a handler. */
export type ActionDispatch = {
  action: string;
  element: HTMLElement;
  event: Event;
  data: Record<string, string>;
};

/**
 * Parse `data-action-*` attributes into camelCase key-value pairs.
 *
 * `data-action-text-set-id="42"` becomes `{ textSetId: "42" }`.
 */
export function parseActionData(element: HTMLElement): Record<string, string> {
  const data: Record<string, string> = {};
  for (let i = 0; i < element.attributes.length; i += 1) {
    const attr = element.attributes[i];
    if (!attr) continue;
    if (attr.name.startsWith("data-action-")) {
      const key = attr.name
        .replace("data-action-", "")
        .replace(/-([a-z])/g, (_m: string, letter: string) =>
          letter.toUpperCase(),
        );
      data[key] = attr.value;
    }
  }
  return data;
}

/**
 * Close the topmost overlay by dispatching `overlay:close` on its element.
 * Overlays mark themselves with `data-overlay-id`.
 */
export function closeTopOverlay(): void {
  const overlays = document.querySelectorAll("[data-overlay-id]");
  if (overlays.length === 0) return;
  const topOverlay = overlays[overlays.length - 1];
  if (!topOverlay) return;
  topOverlay.dispatchEvent(
    new CustomEvent("overlay:close", {
      bubbles: true,
      detail: { id: topOverlay.getAttribute("data-overlay-id") },
    }),
  );
}

/**
 * Resolve a DOM event to an ActionDispatch, or null if no data-action matches.
 */
export function resolveAction(event: Event): ActionDispatch | null {
  const target = event.target;
  if (!(target instanceof Element)) return null;
  const actionElement = target.closest("[data-action]");
  if (!(actionElement instanceof HTMLElement)) return null;
  if (event.type === "click" && actionElement.tagName === "FORM") return null;
  const action = actionElement.getAttribute("data-action");
  if (!action) return null;
  return {
    action,
    element: actionElement,
    event,
    data: parseActionData(actionElement),
  };
}

/**
 * Install document-level listeners for the delegation system.
 * Returns a cleanup function that removes every listener it installed.
 */
export function installEventDelegation(
  onDispatch: (dispatch: ActionDispatch) => void,
  options: { onEscape?: () => void; onOutsideOverlayClick?: () => void } = {},
): () => void {
  const handleActionEvent = (event: Event) => {
    const dispatch = resolveAction(event);
    if (dispatch) onDispatch(dispatch);
  };

  const handleKeyDown = (event: KeyboardEvent) => {
    if (event.key === "Escape") {
      if (options.onEscape) {
        options.onEscape();
      } else {
        closeTopRegistryOverlay();
        closeTopOverlay();
      }
      return;
    }
    if (event.key === "Enter" || event.key === " ") {
      const target = event.target;
      if (!(target instanceof Element)) return;
      if (INTERACTIVE_TAGS.has(target.tagName)) return;
      const dispatch = resolveAction(event);
      if (dispatch) {
        event.preventDefault();
        onDispatch(dispatch);
      }
    }
  };

  const handleMouseDown = (event: MouseEvent) => {
    if (!(event.target instanceof Element)) return;
    const clickedOverlay = event.target.closest("[data-overlay-id]");
    if (clickedOverlay) return;
    if (options.onOutsideOverlayClick) {
      options.onOutsideOverlayClick();
    } else {
      closeTopRegistryOverlay();
      closeTopOverlay();
    }
  };

  for (const eventType of ACTION_EVENT_TYPES) {
    document.addEventListener(eventType, handleActionEvent);
  }
  document.addEventListener("keydown", handleKeyDown);
  document.addEventListener("mousedown", handleMouseDown);

  return () => {
    for (const eventType of ACTION_EVENT_TYPES) {
      document.removeEventListener(eventType, handleActionEvent);
    }
    document.removeEventListener("keydown", handleKeyDown);
    document.removeEventListener("mousedown", handleMouseDown);
  };
}
