/**
 * State owned by the component gallery.
 *
 * The gallery is a standalone dev surface with no server state, so these
 * signals stay module-local — they never join a synced store bundle. Action
 * handlers (actions.ts) reach them by import, the way eal's showcase does.
 * `resetGalleryStores()` exists so the browser/visual test can isolate runs.
 */

import { createForm, setError } from "../../../src/actions";
import { $state } from "../../../src/shared/lib/state.ts";

export type GalleryTheme = "system" | "light" | "dark";

/** The gallery's ActionForm binds to an empty bundle — no store is touched. */
export type GalleryStores = Record<string, never>;

/** Theme override, applied to the panel as `data-polly-theme`. `system` omits
 *  the attribute and lets `prefers-color-scheme` decide. */
export const $galleryTheme = $state<GalleryTheme>("system");
/** Drives the live <Modal> specimen. */
export const $galleryModalOpen = $state<boolean>(false);
/** Drives the live <Dropdown> specimen. */
export const $galleryDropdownOpen = $state<boolean>(false);
/** Selection for the single-select <Select> specimen. */
export const $gallerySelectSingle = $state<Set<string>>(new Set(["comet"]));
/** Selection for the multi-select <Select> specimen. */
export const $gallerySelectMulti = $state<Set<string>>(new Set(["comet", "nebula"]));
/** Selection for the clearable single-select <Select> specimen. Starts empty
 *  so the "Any …" clear option is the active row. */
export const $gallerySelectClearable = $state<Set<string>>(new Set());
/** The live, signal-bound <Checkbox> specimen. */
export const $galleryChecked = $state<boolean>(true);
/** The controlled <TextInput> specimen value. */
export const $galleryText = $state<string>("Controlled value");
/** Last value committed by the <ActionInput> / <ActionSelect> specimens. */
export const $galleryCommitted = $state<string>("—");
/** Active tab id for the <Tabs> specimen. */
export const $galleryTab = $state<string>("overview");
/** Name of the last file picked by the <FileInput> specimen. */
export const $galleryFileName = $state<string>("—");

/**
 * The form behind the <ActionForm> specimen. `createForm` requires `bindStores`
 * before a submit can run; client.tsx binds it to the empty gallery bundle at
 * boot. Its `.actions` are spread into the registry (see actions.ts).
 */
export const galleryForm = createForm<{ fullName: string; email: string }, GalleryStores>({
  name: "gallery-form",
  initialValues: { fullName: "", email: "" },
  onSubmit: ({ values }) => {
    setError(
      `ActionForm submitted — name "${values.fullName || "(empty)"}", ` +
        `email "${values.email || "(empty)"}".`,
      { severity: "info" }
    );
  },
});

/** Reset every gallery signal to its initial value — for test isolation. */
export function resetGalleryStores(): void {
  $galleryTheme.value = "system";
  $galleryModalOpen.value = false;
  $galleryDropdownOpen.value = false;
  $gallerySelectSingle.value = new Set(["comet"]);
  $gallerySelectMulti.value = new Set(["comet", "nebula"]);
  $gallerySelectClearable.value = new Set();
  $galleryChecked.value = true;
  $galleryText.value = "Controlled value";
  $galleryCommitted.value = "—";
  $galleryTab.value = "overview";
  $galleryFileName.value = "—";
  galleryForm.close();
}
