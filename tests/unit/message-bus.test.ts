import { beforeEach, expect, mock, test } from "bun:test";
import { ConnectionError, TimeoutError } from "@/shared/lib/errors";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage } from "@/shared/types/messages";
import { createMockAdapters, createMockPort } from "../helpers/adapters";
import { waitFor } from "../helpers/test-utils";

let bus: MessageBus;

beforeEach(() => {
  const adapters = createMockAdapters();
  bus = new MessageBus("background", adapters);
});

test("MessageBus - send message with automatic ID generation", async () => {
  const handler = mock(async (payload, _message) => {
    expect(payload.type).toBe("SETTINGS_GET");
    return { settings: {} };
  });

  // biome-ignore lint/suspicious/noExplicitAny: Mock handler with flexible return type for test
  bus.on("SETTINGS_GET", handler as any);

  const message: ExtensionMessage = { type: "SETTINGS_GET" };
  const promise = bus.send(message);

  // Simulate receiving response
  await waitFor(10);

  await promise;

  expect(handler).toHaveBeenCalled();
});

test("MessageBus - broadcast to all contexts", () => {
  const sendSpy = mock();
  bus.sendMessage = sendSpy;

  const message: ExtensionMessage = {
    type: "SIGNAL_UPDATE",
    signalId: "test-signal",
    value: { count: 1 },
    source: "background",
  };

  bus.broadcast(message);

  expect(sendSpy).toHaveBeenCalled();
});

test("MessageBus - message handler registration", async () => {
  const handler = mock(async (payload, _message) => {
    expect(payload.selector).toBe(".test");
    return { elements: [] };
  });

  bus.on("DOM_QUERY", handler);

  const message: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  await bus.handleMessage({
    id: "test-id",
    source: "content",
    target: "background",
    timestamp: Date.now(),
    payload: message,
  });

  expect(handler).toHaveBeenCalled();
});

test("MessageBus - request/response correlation", async () => {
  // Set up a handler that will respond
  const handler = mock(async (_payload: ExtensionMessage) => {
    return { elements: [{ tagName: "div" }] };
  });

  // biome-ignore lint/suspicious/noExplicitAny: Mock handler with flexible return type for test
  bus.on("DOM_QUERY", handler as any);

  const message: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  // Simulate the message coming from another context
  // In a real scenario, this would go through chrome.runtime and come back
  const routedMessage = {
    id: "test-id",
    source: "content" as const,
    target: "background" as const,
    timestamp: Date.now(),
    payload: message,
  };

  // biome-ignore lint/suspicious/noExplicitAny: Response type is dynamic in tests
  const response = (await bus.handleMessage(routedMessage)) as any;

  expect(handler).toHaveBeenCalled();
  expect(response.success).toBe(true);
  expect(response.data).toEqual({ elements: [{ tagName: "div" }] });
});

test("MessageBus - timeout handling", async () => {
  const message: ExtensionMessage = { type: "SETTINGS_GET" };

  const promise = bus.send(message, { timeout: 100 });

  // Don't send response - let it timeout
  await expect(promise).rejects.toThrow(TimeoutError);
  await expect(promise).rejects.toMatchObject({
    code: "TIMEOUT_ERROR",
    timeoutMs: 100,
  });
});

test("MessageBus - multiple handlers for same message type", async () => {
  const handler1 = mock(async (_payload, _message) => ({ settings: {} }));
  const handler2 = mock(async (_payload, _message) => ({ settings: {} }));

  // biome-ignore lint/suspicious/noExplicitAny: Mock handler with flexible return type for test
  bus.on("SETTINGS_GET", handler1 as any);
  // biome-ignore lint/suspicious/noExplicitAny: Mock handler with flexible return type for test
  bus.on("SETTINGS_GET", handler2 as any);

  await bus.handleMessage({
    id: "test-id",
    source: "content",
    target: "background",
    timestamp: Date.now(),
    payload: { type: "SETTINGS_GET" },
  });

  // Only the last registered handler should be called
  expect(handler1).not.toHaveBeenCalled();
  expect(handler2).toHaveBeenCalled();
});

// Port management tests removed - port tracking is now handled by MessageRouter
// These methods (registerPort, sendToPort) no longer exist in MessageBus

test("MessageBus - connect creates long-lived port", () => {
  const connectSpy = mock(() => createMockPort("test-connection"));
  const originalConnect = bus.adapters.runtime.connect;
  bus.adapters.runtime.connect = connectSpy;

  bus.connect("test-connection");

  expect(connectSpy).toHaveBeenCalledWith("test-connection");

  // Restore
  bus.adapters.runtime.connect = originalConnect;
});

test("MessageBus - message type safety", async () => {
  // This test verifies compile-time type safety
  const domMessage: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  const apiMessage: ExtensionMessage = {
    type: "API_REQUEST",
    endpoint: "/api/test",
    method: "GET",
  };

  const clipboardMessage: ExtensionMessage = {
    type: "CLIPBOARD_WRITE",
    text: "test",
  };

  // All should be valid ExtensionMessage types
  expect(domMessage.type).toBe("DOM_QUERY");
  expect(apiMessage.type).toBe("API_REQUEST");
  expect(clipboardMessage.type).toBe("CLIPBOARD_WRITE");
});

test("MessageBus - handler error handling", async () => {
  const handler = mock(async () => {
    throw new Error("Handler error");
  });

  // biome-ignore lint/suspicious/noExplicitAny: Mock handler with flexible return type for test
  bus.on("SETTINGS_GET", handler as any);

  const response = (await bus.handleMessage({
    id: "test-id",
    source: "content",
    target: "background",
    timestamp: Date.now(),
    payload: { type: "SETTINGS_GET" },
    // biome-ignore lint/suspicious/noExplicitAny: Response type is dynamic in tests
  })) as any;

  expect(handler).toHaveBeenCalled();
  expect(response.success).toBe(false);
  expect(response.error).toBe("Handler error");
});

test("MessageBus - send with target context", () => {
  const sendSpy = mock();
  const originalSendMessage = bus.sendMessage;
  bus.sendMessage = sendSpy;

  // Just test that sendMessage is called - don't await to avoid timeout
  bus.send({ type: "SETTINGS_GET" }, { target: "popup", tabId: 123 });

  expect(sendSpy).toHaveBeenCalled();
  const call = sendSpy.mock.calls[0]?.[0];
  if (!call) throw new Error("Send call not found");
  expect(call.target).toBe("popup");
  expect(call.tabId).toBe(123);

  // Restore
  bus.sendMessage = originalSendMessage;
});

test("MessageBus - pending request cleanup on timeout", async () => {
  const message: ExtensionMessage = { type: "SETTINGS_GET" };

  const promise = bus.send(message, { timeout: 50 });

  expect(bus.pendingRequests.size).toBeGreaterThan(0);

  await expect(promise).rejects.toThrow(TimeoutError);

  // Pending request should be cleaned up after timeout
  await waitFor(100);
  expect(bus.pendingRequests.size).toBe(0);
});

test("MessageBus - port disconnection rejects pending requests", async () => {
  const mockPort = createMockPort("background");
  const adapters = createMockAdapters();

  // Replace the connect method to return our controlled port
  adapters.runtime.connect = (_name: string) => mockPort;

  const testBus = new MessageBus("content", adapters);

  // Connect to a port
  testBus.connect("content-test");

  // Start a request (shorter timeout to avoid test timeout)
  const promise = testBus.send({ type: "SETTINGS_GET" }, { timeout: 200 });

  // Small delay to ensure request is pending
  await waitFor(10);

  // Disconnect the port
  mockPort.disconnect();

  // Should reject with ConnectionError
  await expect(promise).rejects.toThrow(ConnectionError);
  await expect(promise).rejects.toMatchObject({
    code: "CONNECTION_ERROR",
  });
});

test("MessageBus - broadcast does not wait for responses", () => {
  const sendSpy = mock();
  bus.sendMessage = sendSpy;

  // Broadcast should return immediately
  const result = bus.broadcast({
    type: "SIGNAL_UPDATE",
    signalId: "test",
    value: {},
    source: "background",
  });

  expect(result).toBeUndefined();
  expect(sendSpy).toHaveBeenCalled();
});

test("MessageBus - context identification", () => {
  expect(bus.context).toBe("background");

  const adapters = createMockAdapters();
  const contentBus = new MessageBus("content", adapters);

  expect(contentBus.context).toBe("content");
});
