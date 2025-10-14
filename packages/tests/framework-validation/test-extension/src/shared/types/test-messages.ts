/**
 * Custom Message Types - Example Extension
 *
 * This demonstrates how users would extend the framework with their own messages.
 * These types are separate from the core framework types.
 */

import type { ExtensionMessage } from '@/shared/types/messages'

/**
 * Custom messages for framework validation tests
 * Users would define their own application-specific messages here
 */
export type TestMessages =
  | { type: "TEST_STORAGE"; testValue?: string }
  | { type: "TEST_TABS" }
  | { type: "TEST_MESSAGE_ROUNDTRIP"; data?: unknown }
  | { type: "TEST_SIGNAL_STATE" }
  | { type: "TEST_LOGGER"; message?: string }
  | { type: "TEST_RUNTIME" }
  | { type: "GET_ALL_TEST_RESULTS" }

/**
 * Combined message type - includes both framework and custom messages
 * Users would export this as their main message type
 */
export type AllMessages = ExtensionMessage | TestMessages

/**
 * Type guard to check if a message is a test message
 */
export function isTestMessage(message: ExtensionMessage | TestMessages): message is TestMessages {
  return message.type.startsWith('TEST_') || message.type === 'GET_ALL_TEST_RESULTS'
}
