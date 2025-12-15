/**
 * @fairfox/web-ext
 *
 * Main entry point for framework exports.
 * Users can import from '@fairfox/web-ext' to get common utilities.
 */

// State management
export { $state, $sharedState, $syncedState, $persistedState } from "./shared/lib/state";
export { settings } from "./shared/state/app-state";

// Messaging
export { MessageBus, getMessageBus } from "./shared/lib/message-bus";

// Context helpers (DX improvements)
export { createContext, runInContext } from "./shared/lib/context-helpers";
export type { ContextConfig } from "./shared/lib/context-helpers";

// Test utilities (DX improvements)
export { createTestSuite, quickTest, TestRunner } from "./shared/lib/test-helpers";
export type { TestCase, TestSuite } from "./shared/lib/test-helpers";

// Context-specific helpers (DX improvements)
export type {
  ContentScriptHelpers,
  DevToolsHelpers,
  PopupHelpers,
  OptionsHelpers,
  SidePanelHelpers,
  BackgroundHelpers,
} from "./shared/lib/context-specific-helpers";

// Adapters
export { createChromeAdapters } from "./shared/adapters";
export type { ExtensionAdapters } from "./shared/adapters";

// Errors
export {
  ExtensionError,
  HandlerError,
  TimeoutError,
  ConnectionError,
  ErrorHandler,
} from "./shared/lib/errors";

// Types
export type {
  Context,
  ExtensionMessage,
  MessageResponse,
  RoutedMessage,
  RoutedResponse,
  Settings,
} from "./shared/types/messages";
