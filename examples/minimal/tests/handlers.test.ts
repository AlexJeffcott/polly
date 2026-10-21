/**
 * Tests for Minimal Extension
 *
 * Drives the real handler through a createBackground() bus with mock adapters,
 * the same path the extension entry (src/background/index.ts) takes.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import { createBackground, MessageRouter } from "@fairfox/polly/background";
import type { MessageBus } from "@fairfox/polly/message-bus";
import { createMockAdapters } from "@fairfox/polly/test";
import { type AllMessages, registerPingHandler, user } from "../src/background/handlers";

type Response = { success: boolean; data?: unknown; error?: string };

function send(bus: MessageBus<AllMessages>, payload: AllMessages): Promise<Response> {
  return bus.handleMessage({
    id: crypto.randomUUID(),
    source: "popup",
    targets: ["background"],
    timestamp: Date.now(),
    payload,
  }) as Promise<Response>;
}

test("user starts inactive", () => {
  expect(user.value.active).toBe(false);
});

describe("PING handler", () => {
  let bus: MessageBus<AllMessages>;

  beforeEach(() => {
    MessageRouter.resetInstance();
    bus = createBackground<AllMessages>(createMockAdapters());
    registerPingHandler(bus);
    user.value = { active: true };
  });

  test("returns pong for an active user", async () => {
    const response = await send(bus, { type: "PING" });

    expect(response.success).toBe(true);
    expect(response.data).toEqual({ pong: true });
  });

  test("leaves the user active", async () => {
    await send(bus, { type: "PING" });

    expect(user.value.active).toBe(true);
  });
});
