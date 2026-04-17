/**
 * ConfirmDialog — Promise-returning confirmation primitive.
 *
 * `confirm({ title, body, danger })` returns Promise<boolean>. Opens the
 * rendered `<ConfirmDialog.Host />` modal (which must be mounted once at
 * the app root). User picking confirm or cancel resolves the promise.
 * Escape, backdrop click, and explicit `.dismiss()` resolve false.
 */

import { signal } from "@preact/signals";
import type { JSX } from "preact";
import { Modal } from "./Modal.tsx";
import classes from "./ConfirmDialog.module.css";

type ConfirmRequest = {
  id: number;
  title: string;
  body?: string;
  danger?: boolean;
  confirmLabel?: string;
  cancelLabel?: string;
  resolve: (value: boolean) => void;
};

const pending = signal<ConfirmRequest | null>(null);
const isOpen = signal(false);
let nextId = 0;

export type ConfirmOptions = {
  title: string;
  body?: string;
  danger?: boolean;
  confirmLabel?: string;
  cancelLabel?: string;
};

export function confirm(options: ConfirmOptions): Promise<boolean> {
  return new Promise<boolean>((resolve) => {
    nextId += 1;
    pending.value = {
      id: nextId,
      title: options.title,
      body: options.body,
      danger: options.danger,
      confirmLabel: options.confirmLabel,
      cancelLabel: options.cancelLabel,
      resolve,
    };
    isOpen.value = true;
  });
}

function close(result: boolean): void {
  const current = pending.value;
  if (!current) return;
  isOpen.value = false;
  pending.value = null;
  current.resolve(result);
}

/** Renders the active confirm dialog. Mount once near the app root. */
function Host(): JSX.Element | null {
  const current = pending.value;
  if (!current) return null;
  return (
    <Modal.Root when={isOpen} onClose={() => close(false)}>
      <Modal.Backdrop />
      <Modal.Content>
        <Modal.Header>
          <Modal.Title>{current.title}</Modal.Title>
        </Modal.Header>
        {current.body ? <Modal.Body>{current.body}</Modal.Body> : null}
        <Modal.Footer>
          <div class={classes["actions"]} data-polly-confirm-actions>
            <button
              type="button"
              class={classes["cancel"]}
              data-polly-ui
              data-polly-interactive
              data-polly-confirm-cancel
              onClick={() => close(false)}
            >
              {current.cancelLabel ?? "Cancel"}
            </button>
            <button
              type="button"
              class={current.danger ? classes["confirmDanger"] : classes["confirm"]}
              data-polly-ui
              data-polly-interactive
              data-polly-confirm-ok
              onClick={() => close(true)}
            >
              {current.confirmLabel ?? "OK"}
            </button>
          </div>
        </Modal.Footer>
      </Modal.Content>
    </Modal.Root>
  );
}

export const ConfirmDialog = { Host, confirm };
