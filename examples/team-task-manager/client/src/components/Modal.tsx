import type { ComponentChildren } from "preact";
import { useEffect, useRef } from "preact/hooks";
import { Button } from "./Button";
import { Layout } from "./Layout";

export type ModalProps = {
  isOpen: boolean;
  onClose: () => void;
  title?: string;
  children: ComponentChildren;
  footer?: ComponentChildren;
};

export function Modal({ isOpen, onClose, title, children, footer }: ModalProps) {
  const dialogRef = useRef<HTMLDialogElement>(null);

  // Open/close dialog using native showModal() and close() methods
  useEffect(() => {
    const dialog = dialogRef.current;
    if (!dialog) return;

    if (isOpen) {
      dialog.showModal();
    } else {
      dialog.close();
    }
  }, [isOpen]);

  // Handle close event from dialog (includes Escape key)
  useEffect(() => {
    const dialog = dialogRef.current;
    if (!dialog) return;

    const handleClose = () => {
      onClose();
    };

    dialog.addEventListener("close", handleClose);
    return () => dialog.removeEventListener("close", handleClose);
  }, [onClose]);

  // Handle backdrop click to close modal
  useEffect(() => {
    const dialog = dialogRef.current;
    if (!dialog) return;

    const handleBackdropClick = (e: MouseEvent) => {
      const rect = dialog.getBoundingClientRect();
      const isInDialog =
        e.clientX >= rect.left &&
        e.clientX <= rect.right &&
        e.clientY >= rect.top &&
        e.clientY <= rect.bottom;

      if (!isInDialog) {
        dialog.close();
      }
    };

    dialog.addEventListener("click", handleBackdropClick);
    return () => dialog.removeEventListener("click", handleBackdropClick);
  }, []);

  const rows = title && footer ? "auto 1fr auto" : title ? "auto 1fr" : footer ? "1fr auto" : "1fr";

  return (
    <dialog
      ref={dialogRef}
      class="modal"
      aria-modal="true"
      aria-labelledby={title ? "modal-title" : undefined}
    >
      <Layout rows={rows}>
        {title && (
          <div class="modal-header">
            <h2 id="modal-title">{title}</h2>
            <Button tier="tertiary" size="small" onPress={onClose} aria-label="Close modal">
              ✕
            </Button>
          </div>
        )}

        <div class="modal-body">{children}</div>

        {footer && <div class="modal-footer">{footer}</div>}
      </Layout>
    </dialog>
  );
}
