/**
 * Modal — compound dialog with focus trap, Escape handling, portal,
 * and overlay-stack integration.
 *
 * Root takes a `when` signal (or boolean). When truthy the content mounts
 * into the OverlayRoot portal, focus moves inside, Tab is trapped, Escape
 * fires `data-action="modal:close"` (or the overlay registry's onClose
 * callback), and the body scroll locks.
 */

import type { ReadonlySignal } from "@preact/signals";
import { type ComponentChildren, createContext } from "preact";
import { createPortal } from "preact/compat";
import { useContext, useEffect, useId, useRef, useState } from "preact/hooks";
import { popOverlay, pushOverlay } from "../actions/overlay.ts";
import { installFocusTrap } from "./internal/focus-trap.ts";
import classes from "./Modal.module.css";
import { getOverlayRootNode } from "./OverlayRoot.tsx";

type ModalContext = {
  id: string;
  titleId: string;
  descId: string;
  close: () => void;
};

const Ctx = createContext<ModalContext | null>(null);

function useModal(): ModalContext {
  const ctx = useContext(Ctx);
  if (!ctx) throw new Error("Modal sub-components must render inside <Modal.Root>");
  return ctx;
}

type RootProps = {
  when: ReadonlySignal<boolean> | boolean;
  onClose?: () => void;
  children: ComponentChildren;
  /** Accessible label source: "title" uses the <Modal.Title> id, or pass an explicit label. */
  "aria-label"?: string;
};

function Root({ when, onClose, children, "aria-label": ariaLabel }: RootProps) {
  const id = useId();
  const titleId = `${id}-title`;
  const descId = `${id}-desc`;
  const mountRef = useRef<HTMLDivElement | null>(null);
  const [portalNode, setPortalNode] = useState<HTMLElement | null>(null);

  const isOpen = typeof when === "boolean" ? when : when.value;

  useEffect(() => {
    if (!isOpen) {
      setPortalNode(null);
      return;
    }
    setPortalNode(getOverlayRootNode());
  }, [isOpen]);

  useEffect(() => {
    if (!isOpen || !portalNode) return;
    const entry = { id, onClose };
    pushOverlay(entry);
    const el = mountRef.current;
    const cleanup = el
      ? installFocusTrap(el)
      : () => {
          /* no ref yet */
        };
    return () => {
      cleanup();
      popOverlay(id);
    };
  }, [isOpen, portalNode, id, onClose]);

  if (!isOpen || !portalNode) return null;

  const close = () => {
    onClose?.();
  };

  const ctx: ModalContext = { id, titleId, descId, close };

  const content = (
    <Ctx.Provider value={ctx}>
      <div
        ref={mountRef}
        class={classes["container"]}
        data-polly-ui
        data-polly-modal-content
        data-overlay-id={id}
        data-state="open"
        role="dialog"
        aria-modal="true"
        aria-labelledby={ariaLabel ? undefined : titleId}
        aria-label={ariaLabel}
        aria-describedby={descId}
      >
        {children}
      </div>
    </Ctx.Provider>
  );

  return createPortal(content, portalNode);
}

function Backdrop() {
  const { close } = useModal();
  return (
    <div class={classes["backdrop"]} data-polly-modal-backdrop onClick={close} aria-hidden="true" />
  );
}

function Content({ children }: { children: ComponentChildren }) {
  return (
    <div class={classes["surface"]} data-polly-modal-surface>
      {children}
    </div>
  );
}

function Header({ children }: { children: ComponentChildren }) {
  return (
    <header class={classes["header"]} data-polly-modal-header>
      {children}
    </header>
  );
}

function Title({ children }: { children: ComponentChildren }) {
  const { titleId } = useModal();
  return (
    <h2 id={titleId} class={classes["title"]} data-polly-modal-title>
      {children}
    </h2>
  );
}

function Body({ children }: { children: ComponentChildren }) {
  const { descId } = useModal();
  return (
    <div id={descId} class={classes["body"]} data-polly-modal-body>
      {children}
    </div>
  );
}

function Footer({ children }: { children: ComponentChildren }) {
  return (
    <footer class={classes["footer"]} data-polly-modal-footer>
      {children}
    </footer>
  );
}

type CloseProps = {
  children: ComponentChildren;
  /** Fire a registered data-action instead of calling the onClose callback. */
  action?: string;
};

function Close({ children, action }: CloseProps) {
  const { close } = useModal();
  if (action) {
    return (
      <button
        type="button"
        class={classes["close"]}
        data-polly-ui
        data-polly-interactive
        data-polly-modal-close
        data-action={action}
      >
        {children}
      </button>
    );
  }
  return (
    <button
      type="button"
      class={classes["close"]}
      data-polly-ui
      data-polly-interactive
      data-polly-modal-close
      onClick={close}
    >
      {children}
    </button>
  );
}

export const Modal = {
  Root,
  Backdrop,
  Content,
  Header,
  Title,
  Body,
  Footer,
  Close,
};
