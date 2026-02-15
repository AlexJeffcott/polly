// Background helper - simplifies background script setup

import type { ExtensionAdapters } from "../shared/adapters";
import type { MessageBus } from "../shared/lib/message-bus";
import { getMessageBus } from "../shared/lib/message-bus";
import type { BaseMessage, ExtensionMessage } from "../shared/types/messages";
import { MessageRouter } from "./message-router";

/**
 * Initialize background script with message router.
 *
 * This is the recommended way to setup your background script.
 * It automatically creates the message bus and router.
 *
 * @param adapters - Optional extension adapters. If not provided, Chrome adapters will be used.
 * @returns MessageBus instance for registering handlers
 *
 * @example
 * ```typescript
 * // src/background/index.ts
 * import { createBackground } from '@fairfox/web-ext/background'
 *
 * const bus = createBackground()
 *
 * bus.on('MY_MESSAGE', async (payload) => {
 *   return { success: true }
 * })
 * ```
 *
 * @example With custom message types
 * ```typescript
 * type MyMessages = { type: 'MY_MESSAGE'; data: string }
 * const bus = createBackground<MyMessages>()
 * ```
 *
 * @example With mock adapters for testing
 * ```typescript
 * import { createMockAdapters } from '@fairfox/polly/test'
 * const bus = createBackground(createMockAdapters())
 * ```
 */
export function createBackground<TMessage extends BaseMessage = ExtensionMessage>(
  adapters?: ExtensionAdapters
): MessageBus<TMessage> {
  // Create MessageBus without setting up listeners (MessageRouter will handle that)
  const bus = getMessageBus<TMessage>("background", adapters, { skipListenerSetup: true });

  // Initialize MessageRouter to handle all message routing (generic type matches)
  new MessageRouter<TMessage>(bus);

  return bus;
}

export { getMessageBus } from "../shared/lib/message-bus";
// Re-export for convenience
export { MessageRouter } from "./message-router";
