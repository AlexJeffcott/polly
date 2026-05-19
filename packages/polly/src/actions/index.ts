/**
 * Public API for `@fairfox/polly/actions`.
 *
 * The action registry pattern: one document listener, one typed registry,
 * components are logic-free consumers of signals that emit `data-action`.
 */

export {
  clearError,
  type ErrorEntry,
  type ErrorSeverity,
  errorState,
  setError,
  submitError,
} from "./error.ts";
export {
  ACTION_EVENT_TYPES,
  type ActionDispatch,
  closeTopOverlay as closeTopOverlayViaDom,
  INTERACTIVE_TAGS,
  installEventDelegation,
  parseActionData,
  resolveAction,
} from "./event-delegation.ts";
export {
  createForm,
  createFormSet,
  type FormConfig,
  type FormOpenContext,
  type FormSet,
  type FormStore,
  type FormSubmitContext,
} from "./form.ts";
export {
  closeTopOverlay,
  hasOpenOverlay,
  type OverlayEntry,
  overlayStack,
  popOverlay,
  pushOverlay,
  resetOverlayStack,
  topOverlay,
} from "./overlay.ts";
export type {
  ActionContext,
  ActionHandler,
  ActionRegistry,
} from "./registry.ts";
export { createStore, StoreProvider, type StoreProviderProps, useStores } from "./store.tsx";

export {
  createMockElement,
  createMockStores,
  createMockSubmitEvent,
  runAction,
} from "./testing.ts";
