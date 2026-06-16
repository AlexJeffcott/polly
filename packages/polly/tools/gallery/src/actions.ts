/**
 * Actions for the gallery's interactive specimens. Every handler drives a
 * module-local signal (stores.ts) or a polly overlay primitive — none touches a
 * store bundle, so the gallery stays a self-contained dev surface. Spreading
 * `galleryForm.actions` adds the auto-registered `gallery-form:{open,close,
 * submit}` handlers. client.tsx wires this registry into the document via
 * `installEventDelegation`, exactly as a real consumer app would.
 */

import type { ActionRegistry, ErrorSeverity } from "../../../src/actions";
import { setError } from "../../../src/actions";
import { confirm } from "../../../src/polly-ui";
import {
  $galleryCommitted,
  $galleryModalOpen,
  $galleryTab,
  $galleryTheme,
  type GalleryStores,
  type GalleryTheme,
  galleryForm,
} from "./stores.ts";

const THEMES: readonly GalleryTheme[] = ["system", "light", "dark"];
const SEVERITIES: readonly ErrorSeverity[] = ["info", "warning", "error"];

export const GALLERY_ACTIONS: ActionRegistry<GalleryStores> = {
  ...galleryForm.actions,

  "gallery:set-theme": ({ data }) => {
    const theme = data["theme"];
    if (theme === "system" || theme === "light" || theme === "dark") {
      $galleryTheme.value = theme;
    }
  },

  "gallery:set-tab": ({ data }) => {
    const id = data["id"];
    if (typeof id === "string") $galleryTab.value = id;
  },

  "gallery:modal-open": () => {
    $galleryModalOpen.value = true;
  },

  "gallery:commit": ({ data }) => {
    const value = data["value"];
    if (typeof value === "string") $galleryCommitted.value = value;
  },

  "gallery:toast": ({ data }) => {
    const severity = SEVERITIES.find((s) => s === data["severity"]) ?? "info";
    setError(`This is a ${severity} toast — click it or wait for it to dismiss.`, {
      severity,
    });
  },

  "gallery:confirm": async ({ data }) => {
    const danger = data["danger"] === "true";
    const ok = await confirm({
      title: danger ? "Delete this item?" : "Save your changes?",
      body: danger
        ? "This cannot be undone. The item will be permanently removed."
        : "Your changes will be applied immediately.",
      danger,
      confirmLabel: danger ? "Delete" : "Save",
    });
    setError(`ConfirmDialog resolved ${String(ok)}.`, { severity: ok ? "info" : "warning" });
  },
};

/** The theme cycle, exposed so the panel can render one button per option. */
export { THEMES };
