/**
 * @fairfox/polly/ui — compound UI primitives.
 *
 * Every primitive is built on @fairfox/polly/actions: data-action hooks
 * route events into the consumer's action registry, semantic tokens
 * drive all visual values, and the <Layout> primitive owns every
 * layouting concern. Ship styles.css and theme.css alongside to pick up
 * the default look; redefine variables to re-theme.
 */

export { ActionForm, type ActionFormProps } from "./ActionForm.tsx";
export {
  ActionInput,
  type ActionInputProps,
  type ActionInputSaveOn,
  type ActionInputVariant,
} from "./ActionInput.tsx";
export { ConfirmDialog, type ConfirmOptions, confirm } from "./ConfirmDialog.tsx";
export { Layout, type LayoutProps } from "./Layout.tsx";
export { Modal } from "./Modal.tsx";
export { getOverlayRootNode, OverlayRoot } from "./OverlayRoot.tsx";
export { TextInput, type TextInputProps } from "./TextInput.tsx";
export { Toast, type ToastViewportProps } from "./Toast.tsx";
