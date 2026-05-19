/**
 * Toast — consumer-facing surface for the global errorState.
 *
 * Renders every entry of the `errorState` signal into a viewport mounted
 * inside OverlayRoot. `aria-live` is polite for info/warning and
 * assertive for error severity. Each item auto-dismisses after
 * `autoDismissMs` unless the user hovers the viewport. Clicking a
 * toast or its close button removes that single entry.
 */

import type { JSX } from "preact";
import { createPortal } from "preact/compat";
import { useEffect, useState } from "preact/hooks";
import { clearError, type ErrorEntry, errorState } from "../actions/error.ts";
import { getOverlayRootNode } from "./OverlayRoot.tsx";
import { Surface } from "./Surface.tsx";
import classes from "./Toast.module.css";

export type ToastViewportProps = {
  autoDismissMs?: number;
  className?: string;
};

function Viewport(props: ToastViewportProps): JSX.Element | null {
  const autoDismissMs = props.autoDismissMs ?? 5000;
  const [portalNode, setPortalNode] = useState<HTMLElement | null>(null);
  const [paused, setPaused] = useState(false);
  const entries = errorState.value;

  useEffect(() => {
    setPortalNode(getOverlayRootNode());
  }, []);

  useEffect(() => {
    if (paused || entries.length === 0) return;
    const head = entries[0];
    if (!head) return;
    const timer = window.setTimeout(() => {
      clearError(head.id);
    }, autoDismissMs);
    return () => window.clearTimeout(timer);
  }, [paused, entries, autoDismissMs]);

  if (!portalNode) return null;

  const content = (
    // biome-ignore lint/a11y/noStaticElementInteractions: viewport pauses auto-dismiss on hover; it is a container, not an interactive control itself.
    <div
      class={`${classes["viewport"]} ${props.className ?? ""}`.trim()}
      data-polly-ui
      data-polly-toast-viewport
      onMouseEnter={() => setPaused(true)}
      onMouseLeave={() => setPaused(false)}
    >
      {entries.map((entry) => (
        <ToastItem key={entry.id} entry={entry} />
      ))}
    </div>
  );
  return createPortal(content, portalNode);
}

function ToastItem({ entry }: { entry: ErrorEntry }): JSX.Element {
  const liveness = entry.severity === "error" ? "assertive" : "polite";
  return (
    <Surface
      variant="raised"
      padding="var(--polly-space-md) var(--polly-space-lg)"
      className={classes["item"]}
      data-polly-ui
      data-polly-toast-item
      data-severity={entry.severity}
      role={entry.severity === "error" ? "alert" : "status"}
      aria-live={liveness}
    >
      <span class={classes["message"]}>{entry.message}</span>
      <button
        type="button"
        class={classes["close"]}
        data-polly-ui
        data-polly-interactive
        data-polly-toast-close
        onClick={() => clearError(entry.id)}
        aria-label="Dismiss"
      >
        ×
      </button>
    </Surface>
  );
}

export const Toast = { Viewport };
