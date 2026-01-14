/**
 * @fairfox/web-ext
 *
 * Main entry point for framework exports.
 * Users can import from '@fairfox/web-ext' to get common utilities.
 */

export type { ExtensionAdapters } from "./shared/adapters";
// Adapters
export { createChromeAdapters } from "./shared/adapters";
export type { ContextConfig } from "./shared/lib/context-helpers";

// Context helpers (DX improvements)
export { createContext, runInContext } from "./shared/lib/context-helpers";
// Context-specific helpers (DX improvements)
export type {
  BackgroundHelpers,
  ContentScriptHelpers,
  DevToolsHelpers,
  OptionsHelpers,
  PopupHelpers,
  SidePanelHelpers,
} from "./shared/lib/context-specific-helpers";
// Errors
export {
  ConnectionError,
  ErrorHandler,
  ExtensionError,
  HandlerError,
  TimeoutError,
} from "./shared/lib/errors";
// Messaging
export { getMessageBus, MessageBus } from "./shared/lib/message-bus";
// State management
export { $persistedState, $sharedState, $state, $syncedState } from "./shared/lib/state";
// Validation helpers
export { validateArray, validateEnum, validatePartial, validateShape } from "./shared/lib/validation";
// Runtime constraint checking
export {
  checkPostconditions,
  checkPreconditions,
  clearConstraints,
  isRuntimeConstraintsEnabled,
  registerConstraint,
  registerConstraints,
} from "./shared/lib/constraints";
export type { TestCase, TestSuite } from "./shared/lib/test-helpers";
// Test utilities (DX improvements)
export { createTestSuite, quickTest, TestRunner } from "./shared/lib/test-helpers";
export { settings } from "./shared/state/app-state";

// Types
export type {
  Context,
  ExtensionMessage,
  MessageResponse,
  RoutedMessage,
  RoutedResponse,
  Settings,
} from "./shared/types/messages";
