import { afterEach, beforeEach, expect, mock, test } from "bun:test";
import { ConnectionError, TimeoutError } from "@/shared/lib/errors";
import { globalExecutionTracker } from "@/shared/lib/handler-execution-tracker";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage, RoutedMessage } from "@/shared/types/messages";
import { createMockAdapters, createMockPort } from "@fairfox/polly/test";
import { waitFor } from "@fairfox/polly/test";

let bus: MessageBus;

beforeEach(() => {
  const adapters = createMockAdapters();
  bus = new MessageBus("background", adapters);
});

afterEach(() => {
  bus.destroy();
  globalExecutionTracker.reset();
});

test("MessageBus - send message with automatic ID generation", async () => {
  const handler = mock(async (payload: ExtensionMessage) => {
    expect(payload.type).toBe("SETTINGS_GET");
    return { settings: {} };
  });

  bus.on("SETTINGS_GET", handler);

  const message: ExtensionMessage = { type: "SETTINGS_GET" };
  const promise = bus.send(message, { target: "background" });

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
    targets: ["background"],
    timestamp: Date.now(),
    payload: message,
  });

  expect(handler).toHaveBeenCalled();
});

test("MessageBus - request/response correlation", async () => {
  // Set up a handler that will respond
  const handler = mock(async (_payload: ExtensionMessage) => {
    return {
      elements: [
        {
          tag: "div",
          text: "Test",
          html: "<div>Test</div>",
          attrs: {},
        },
      ],
    };
  });

  bus.on("DOM_QUERY", handler);

  const message: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  // Simulate the message coming from another context
  // In a real scenario, this would go through chrome.runtime and come back
  const routedMessage: RoutedMessage<ExtensionMessage> = {
    id: "test-id",
    source: "content",
    targets: ["background"],
    timestamp: Date.now(),
    payload: message,
  };

  const response = await bus.handleMessage(routedMessage);

  expect(handler).toHaveBeenCalled();
  if (
    typeof response === "object" &&
    response !== null &&
    "success" in response &&
    response.success === true
  ) {
    expect(response.success).toBe(true);
    if ("data" in response) {
      expect(response.data).toEqual({
        elements: [
          {
            tag: "div",
            text: "Test",
            html: "<div>Test</div>",
            attrs: {},
          },
        ],
      });
    }
  } else {
    throw new Error("Response does not match expected shape");
  }
});

test("MessageBus - timeout handling", async () => {
  const message: ExtensionMessage = { type: "SETTINGS_GET" };

  const promise = bus.send(message, { target: "background", timeout: 100 });

  // Don't send response - let it timeout
  await expect(promise).rejects.toThrow(TimeoutError);
  await expect(promise).rejects.toMatchObject({
    code: "TIMEOUT_ERROR",
    timeoutMs: 100,
  });
});

test("MessageBus - multiple handlers for same message type", async () => {
  const handler1 = mock(async (_payload: ExtensionMessage) => ({ settings: {} }));
  const handler2 = mock(async (_payload: ExtensionMessage) => ({ settings: {} }));

  bus.on("SETTINGS_GET", handler1);
  bus.on("SETTINGS_GET", handler2);

  await bus.handleMessage({
    id: "test-id",
    source: "content",
    targets: ["background"],
    timestamp: Date.now(),
    payload: { type: "SETTINGS_GET" },
  });

  // For targeted messages, first registered handler is called
  expect(handler1).toHaveBeenCalled();
  expect(handler2).not.toHaveBeenCalled();
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
  const handler = mock(async (_payload: ExtensionMessage) => {
    throw new Error("Handler error");
  });

  bus.on("SETTINGS_GET", handler);

  const routedMessage: RoutedMessage<ExtensionMessage> = {
    id: "test-id",
    source: "content",
    targets: ["background"],
    timestamp: Date.now(),
    payload: { type: "SETTINGS_GET" },
  };

  const response = await bus.handleMessage(routedMessage);

  expect(handler).toHaveBeenCalled();
  if (
    typeof response === "object" &&
    response !== null &&
    "success" in response &&
    response.success === false
  ) {
    expect(response.success).toBe(false);
    if ("error" in response) {
      expect(response.error).toBe("Handler error");
    }
  } else {
    throw new Error("Response does not match expected shape");
  }
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
  expect(call.targets).toEqual(["popup"]);
  expect(call.tabId).toBe(123);

  // Restore
  bus.sendMessage = originalSendMessage;
});

test("MessageBus - pending request cleanup on timeout", async () => {
  const message: ExtensionMessage = { type: "SETTINGS_GET" };

  const promise = bus.send(message, { target: "background", timeout: 50 });

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
  const promise = testBus.send({ type: "SETTINGS_GET" }, { target: "background", timeout: 200 });

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
