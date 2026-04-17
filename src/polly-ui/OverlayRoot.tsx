/**
 * OverlayRoot — portal target for stacked overlays.
 *
 * Apps render <OverlayRoot /> once, typically as the last child of the
 * app root. Modal, ConfirmDialog, and Toast portal into this element;
 * the scroll lock toggles based on the overlay registry count.
 */

import { effect } from "@preact/signals";
import { useEffect, useRef } from "preact/hooks";
import { hasOpenOverlay } from "../actions/overlay.ts";
import { acquireScrollLock } from "./internal/scroll-lock.ts";
import classes from "./OverlayRoot.module.css";

export function OverlayRoot() {
  const ref = useRef<HTMLDivElement>(null);

  useEffect(() => {
    let release: (() => void) | null = null;
    const dispose = effect(() => {
      if (hasOpenOverlay()) {
        if (!release) release = acquireScrollLock();
      } else if (release) {
        release();
        release = null;
      }
    });
    return () => {
      dispose();
      release?.();
    };
  }, []);

  return (
    <div
      ref={ref}
      class={classes["root"]}
      data-polly-ui
      data-polly-overlay-root
    />
  );
}

/** Get the mount node for portaled overlays. Returns null before mount. */
export function getOverlayRootNode(): HTMLElement | null {
  return document.querySelector<HTMLElement>("[data-polly-overlay-root]");
}
