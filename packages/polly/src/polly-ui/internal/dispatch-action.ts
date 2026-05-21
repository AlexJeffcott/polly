/**
 * Fire a named action through the global event-delegation registry.
 *
 * The Action* primitives (<ActionInput>, <ActionSelect>) commit by
 * clicking a detached `<button data-action="…">` carrying data-action-*
 * attributes; the delegated click listener routes it into the
 * consumer's action registry with no extra wiring. Centralised here so
 * every Action* primitive dispatches identically.
 *
 * Keys in `data` are camelCase and converted to dash-case attribute
 * names — `actionData={{ taskId }}` becomes `data-action-task-id`.
 */

export function dispatchAction(action: string, data: Record<string, string>): void {
  const hidden = document.createElement("button");
  hidden.setAttribute("data-action", action);
  for (const [key, value] of Object.entries(data)) {
    const dashKey = key.replace(/[A-Z]/g, (m) => `-${m.toLowerCase()}`);
    hidden.setAttribute(`data-action-${dashKey}`, value);
  }
  hidden.style.position = "fixed";
  hidden.style.opacity = "0";
  hidden.style.pointerEvents = "none";
  hidden.tabIndex = -1;
  document.body.appendChild(hidden);
  try {
    hidden.click();
  } finally {
    hidden.remove();
  }
}
