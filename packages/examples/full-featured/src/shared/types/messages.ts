/**
 * Custom message types for test extension
 */

import type { ExtensionMessage } from "@fairfox/web-ext/types";

export type TestMessages =
  | { type: "TEST_STORAGE"; testValue?: string }
  | { type: "TEST_TABS" }
  | { type: "TEST_MESSAGE_ROUNDTRIP"; data?: unknown }
  | { type: "TEST_SIGNAL_STATE" }
  | { type: "TEST_RUNTIME" }
  | { type: "GET_ALL_TEST_RESULTS" };

// Combined message type - includes both framework and custom messages
export type AllMessages = ExtensionMessage | TestMessages;
