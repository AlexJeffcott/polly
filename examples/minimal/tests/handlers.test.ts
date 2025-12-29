/**
 * Tests for Minimal Extension
 *
 * Demonstrates basic testing with @fairfox/polly/test
 */

import { beforeEach, describe, expect, test } from "bun:test";
import { createMockAdapters, type MockExtensionAdapters } from "@fairfox/polly/test";
import { MessageBus } from "@fairfox/polly/message-bus";
import type { ExtensionMessage } from "@fairfox/polly/types";

type CustomMessages = { type: "PING" };
type AllMessages = ExtensionMessage | CustomMessages;

describe("PING Handler Logic", () => {
  test("handler returns pong", async () => {
    // Simulate handler logic
    const handler = async () => ({ pong: true });

    const response = await handler();
    expect(response.pong).toBe(true);
  });
});

describe("Mock Adapters", () => {
  let adapters: MockExtensionAdapters;

  beforeEach(() => {
    adapters = createMockAdapters();
  });

  test("can use mock storage", async () => {
    await adapters.storage.set({ key: "value" });

    const result = await adapters.storage.get("key");
    expect(result.key).toBe("value");
  });
});
