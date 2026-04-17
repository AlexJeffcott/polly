/**
 * Focus trap.
 *
 * Keeps Tab / Shift+Tab inside a root element. Returns a cleanup that
 * restores focus to the element that was active before the trap mounted.
 * Simple and synchronous — assumes a single active trap per OverlayRoot
 * and lets the overlay registry in `@fairfox/polly/actions` enforce that
 * at the stack level.
 */

const FOCUSABLE_SELECTOR = [
  "a[href]",
  "area[href]",
  "button:not([disabled])",
  "input:not([disabled]):not([type=hidden])",
  "select:not([disabled])",
  "textarea:not([disabled])",
  "iframe",
  "object",
  "embed",
  '[tabindex]:not([tabindex="-1"])',
  "[contenteditable]",
].join(",");

function getFocusable(root: HTMLElement): HTMLElement[] {
  const nodes = Array.from(
    root.querySelectorAll<HTMLElement>(FOCUSABLE_SELECTOR),
  );
  return nodes.filter(
    (el) =>
      !el.hasAttribute("disabled") &&
      el.getAttribute("aria-hidden") !== "true",
  );
}

export function installFocusTrap(root: HTMLElement): () => void {
  const previousActive = (document.activeElement instanceof HTMLElement
    ? document.activeElement
    : null) as HTMLElement | null;

  // Move focus into the root if it's not already.
  const focusable = getFocusable(root);
  const first = focusable[0] ?? root;
  if (!root.contains(document.activeElement)) {
    first.focus();
  }

  function handleKeyDown(event: KeyboardEvent): void {
    if (event.key !== "Tab") return;
    const items = getFocusable(root);
    if (items.length === 0) {
      event.preventDefault();
      return;
    }
    const firstItem = items[0];
    const lastItem = items[items.length - 1];
    if (!firstItem || !lastItem) return;
    const active = document.activeElement;
    if (event.shiftKey) {
      if (active === firstItem || !root.contains(active)) {
        event.preventDefault();
        lastItem.focus();
      }
    } else {
      if (active === lastItem) {
        event.preventDefault();
        firstItem.focus();
      }
    }
  }

  document.addEventListener("keydown", handleKeyDown);

  return () => {
    document.removeEventListener("keydown", handleKeyDown);
    if (previousActive && document.contains(previousActive)) {
      previousActive.focus();
    }
  };
}
