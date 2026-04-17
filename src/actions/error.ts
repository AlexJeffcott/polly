/**
 * Global error surface for action handlers.
 *
 * Actions that fail set the errorState signal via `submitError`; a `<Toast>`
 * component consumes that signal and renders a dismissable message. Handlers
 * that catch expected failures (validation, quota) may call `setError` directly.
 */

import { signal } from "@preact/signals";

export type ErrorSeverity = "error" | "warning" | "info";

export type ErrorEntry = {
  id: string;
  message: string;
  severity: ErrorSeverity;
  action?: string;
  createdAt: number;
};

export const errorState = signal<ErrorEntry[]>([]);

let nextId = 0;
function allocId(): string {
  nextId += 1;
  return `polly-err-${nextId}`;
}

export function setError(
  message: string,
  opts: { severity?: ErrorSeverity; action?: string } = {},
): string {
  const entry: ErrorEntry = {
    id: allocId(),
    message,
    severity: opts.severity ?? "error",
    action: opts.action,
    createdAt: Date.now(),
  };
  errorState.value = [...errorState.value, entry];
  return entry.id;
}

export function clearError(id?: string): void {
  if (id === undefined) {
    errorState.value = [];
    return;
  }
  errorState.value = errorState.value.filter((e) => e.id !== id);
}

/**
 * Convenience wrapper for an action's catch block.
 * Logs the action name + error and surfaces a user-visible message.
 */
export function submitError(action: string, err: unknown): string {
  const message = err instanceof Error ? err.message : String(err);
  return setError(message, { action, severity: "error" });
}
