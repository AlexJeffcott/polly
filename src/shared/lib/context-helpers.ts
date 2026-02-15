/**
 * Context Helpers - DX Improvements for Extension Context Initialization
 *
 * Provides utilities to reduce boilerplate when initializing extension contexts.
 */

import type { ExtensionAdapters } from "../adapters";
import type { BaseMessage, Context, ExtensionMessage } from "../types/messages";
import { getMessageBus, type MessageBus } from "./message-bus";

export interface ContextConfig<TMessage extends BaseMessage = ExtensionMessage> {
  /**
   * Called when the context is initialized.
   * Use this to register handlers, setup UI, etc.
   */
  onInit?: (bus: MessageBus<TMessage>) => Promise<void> | void;

  /**
   * Called when an error occurs during initialization or runtime.
   */
  onError?: (error: Error, bus: MessageBus<TMessage>) => void;

  /**
   * Whether to wait for DOM to be ready before initializing.
   * Only applies to contexts with a window (popup, options, devtools, sidepanel).
   * @default true
   */
  waitForDOM?: boolean;

  /**
   * Custom logger prefix.
   * @default `[${context}]`
   */
  logPrefix?: string;

  /**
   * Optional extension adapters. If not provided, Chrome adapters will be used.
   * Useful for testing with mock adapters.
   */
  adapters?: ExtensionAdapters;
}

/**
 * Create and initialize an extension context with reduced boilerplate.
 *
 * @param context - The extension context (popup, background, content, etc.)
 * @param config - Configuration options including optional adapters
 * @returns MessageBus instance for the context
 *
 * @example
 * ```typescript
 * // src/popup/index.ts
 * createContext<MyMessages>('popup', {
 *   async onInit(bus) {
 *     registerHandlers(bus)
 *     setupUI()
 *   },
 *   onError(err) {
 *     console.error('Popup failed:', err)
 *   }
 * })
 * ```
 *
 * @example With mock adapters for testing
 * ```typescript
 * import { createMockAdapters } from '@fairfox/polly/test'
 *
 * createContext('popup', {
 *   adapters: createMockAdapters(),
 *   async onInit(bus) {
 *     // Your initialization code
 *   }
 * })
 * ```
 */
export function createContext<TMessage extends BaseMessage = ExtensionMessage>(
  context: Context,
  config: ContextConfig<TMessage> = {}
): MessageBus<TMessage> {
  const {
    onInit,
    onError,
    waitForDOM = true,
    logPrefix = `[${context.charAt(0).toUpperCase() + context.slice(1)}]`,
    adapters,
  } = config;

  const bus = getMessageBus<TMessage>(context, adapters);

  // Setup error handler if provided
  if (onError) {
    bus.onError(onError);
  }

  const initialize = async () => {
    try {
      if (onInit) {
        await onInit(bus);
      }
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`${logPrefix} Initialization failed:`, err);

      if (onError) {
        onError(err, bus);
      } else {
        throw err;
      }
    }
  };

  // Contexts with DOM need to wait for DOMContentLoaded
  const contextsWithDOM: Context[] = ["popup", "options", "devtools", "sidepanel", "content"];

  if (typeof window !== "undefined" && contextsWithDOM.includes(context) && waitForDOM) {
    if (document.readyState === "loading") {
      document.addEventListener("DOMContentLoaded", () => {
        initialize().catch((err) => {
          console.error(`${logPrefix} Uncaught initialization error:`, err);
        });
      });
    } else {
      // DOM already loaded
      initialize().catch((err) => {
        console.error(`${logPrefix} Uncaught initialization error:`, err);
      });
    }
  } else {
    // Background, worker, or already initialized
    initialize().catch((err) => {
      console.error(`${logPrefix} Uncaught initialization error:`, err);
    });
  }

  return bus;
}

/**
 * Helper to run code only in specific contexts.
 * Useful for shared modules that need context-specific behavior.
 *
 * @example
 * ```typescript
 * // shared/features/analytics.ts
 * const bus = createContext('popup', { ... })
 *
 * if (bus.context === 'popup' || bus.context === 'options') {
 *   setupUI()
 * }
 * ```
 *
 * @deprecated Use bus.context directly instead. This function cannot reliably detect context.
 */
export function runInContext(
  context: Context,
  contexts: Context | Context[],
  fn: (bus: MessageBus) => void | Promise<void>,
  adapters?: ExtensionAdapters
): void {
  const targetContexts = Array.isArray(contexts) ? contexts : [contexts];

  if (targetContexts.includes(context)) {
    const bus = getMessageBus(context, adapters);
    Promise.resolve(fn(bus)).catch(() => {
      // Error already handled by global error handler
    });
  }
}
