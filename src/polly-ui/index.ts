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
export { Badge, type BadgeProps, type BadgeVariant } from "./Badge.tsx";
export {
  Button,
  type ButtonColor,
  type ButtonProps,
  type ButtonSize,
  type ButtonTier,
} from "./Button.tsx";
export { Checkbox, type CheckboxProps } from "./Checkbox.tsx";
export { Collapsible, type CollapsibleProps } from "./Collapsible.tsx";
export { ConfirmDialog, type ConfirmOptions, confirm } from "./ConfirmDialog.tsx";
export { Dropdown, type DropdownProps } from "./Dropdown.tsx";
export { Layout, type LayoutProps } from "./Layout.tsx";
export { Modal } from "./Modal.tsx";
export { getOverlayRootNode, OverlayRoot } from "./OverlayRoot.tsx";
export { Select, type SelectOption, type SelectProps } from "./Select.tsx";
export { Skeleton, type SkeletonProps, type SkeletonVariant } from "./Skeleton.tsx";
export { Surface, type SurfaceProps, type SurfaceVariant } from "./Surface.tsx";
export { type Tab, Tabs, type TabsProps } from "./Tabs.tsx";
export { TextInput, type TextInputProps } from "./TextInput.tsx";
export { Toast, type ToastViewportProps } from "./Toast.tsx";
export { Toggle, type ToggleProps } from "./Toggle.tsx";
