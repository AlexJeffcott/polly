/**
 * Overlay registry.
 *
 * Tracks the stack of open overlays (modals, popovers, confirm dialogs) so
 * Escape can close the topmost and `data-overlay-id`-based DOM scans have
 * a mirror in memory. Each entry stores an id plus an optional close
 * callback; `closeTopOverlay` invokes the callback and pops the entry.
 */

import { signal } from "@preact/signals";

export type OverlayEntry = {
  id: string;
  onClose?: () => void;
};

const stack = signal<OverlayEntry[]>([]);

/** Current overlay stack as a read-only snapshot. */
export function overlayStack(): readonly OverlayEntry[] {
  return stack.value;
}

/** Is any overlay currently open? */
export function hasOpenOverlay(): boolean {
  return stack.value.length > 0;
}

/** The top of the stack, or undefined if empty. */
export function topOverlay(): OverlayEntry | undefined {
  const s = stack.value;
  return s[s.length - 1];
}

/** Push an overlay onto the stack. Returns the popped entry when closed. */
export function pushOverlay(entry: OverlayEntry): void {
  stack.value = [...stack.value, entry];
}

/** Pop a specific overlay by id (or the top if no id given). */
export function popOverlay(id?: string): OverlayEntry | undefined {
  const s = stack.value;
  if (s.length === 0) return undefined;
  if (id === undefined) {
    const top = s[s.length - 1];
    stack.value = s.slice(0, -1);
    return top;
  }
  const idx = s.findIndex((e) => e.id === id);
  if (idx === -1) return undefined;
  const entry = s[idx];
  stack.value = [...s.slice(0, idx), ...s.slice(idx + 1)];
  return entry;
}

/** Close the top overlay by calling its onClose and popping it. */
export function closeTopOverlay(): OverlayEntry | undefined {
  const top = topOverlay();
  if (!top) return undefined;
  top.onClose?.();
  return popOverlay(top.id);
}

/** Reset the stack. Intended for tests. */
export function resetOverlayStack(): void {
  stack.value = [];
}
