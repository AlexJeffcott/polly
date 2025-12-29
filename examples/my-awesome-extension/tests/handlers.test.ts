/**
 * Tests for My Awesome Extension
 *
 * Demonstrates basic testing with @fairfox/polly/test
 */

import { beforeEach, describe, expect, test } from "bun:test";
import { type MockExtensionAdapters, createMockAdapters } from "@fairfox/polly/test";

describe("Handler Logic", () => {
  test("PING handler returns pong", async () => {
    // Simulate handler logic
    const handler = async () => {
      return { success: true, message: "pong" };
    };

    const response = await handler();

    expect(response.success).toBe(true);
    expect(response.message).toBe("pong");
  });
});

describe("Mock Adapters", () => {
  let adapters: MockExtensionAdapters;

  beforeEach(() => {
    adapters = createMockAdapters();
  });

  test("can use mock storage", async () => {
    // Store data using mock storage
    await adapters.storage.set({ customData: "test value" });

    // Retrieve it
    const result = await adapters.storage.get("customData");
    expect(result.customData).toBe("test value");
  });

  test("can simulate handler with storage", async () => {
    // Simulate a handler function that uses storage
    const saveHandler = async (value: string) => {
      await adapters.storage.set({ data: value });
      return { success: true };
    };

    // Call the handler
    await saveHandler("saved data");

    // Verify storage
    const stored = await adapters.storage.get("data");
    expect(stored.data).toBe("saved data");
  });
});
