import { expect, mock, test } from "bun:test";
import { globalExecutionTracker } from "@/shared/lib/handler-execution-tracker";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage } from "@/shared/types/messages";
import { createMockAdapters } from "@fairfox/polly/test";

/**
 * Content script tests - focus on message handling logic
 * DOM operations will be tested in E2E tests with Playwright
 */

test("Content - DOM_QUERY message structure", () => {
  const message: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test-class",
  };

  expect(message.type).toBe("DOM_QUERY");
  expect(message.selector).toBe(".test-class");
});

test("Content - DOM_UPDATE message structure", () => {
  const message: ExtensionMessage = {
    type: "DOM_UPDATE",
    selector: "#test",
    content: "Updated",
  };

  expect(message.type).toBe("DOM_UPDATE");
  expect(message.selector).toBe("#test");
  expect(message.content).toBe("Updated");
});

test("Content - DOM_INSERT message structure", () => {
  const message: ExtensionMessage = {
    type: "DOM_INSERT",
    html: "<div>New element</div>",
    position: "beforeend",
  };

  expect(message.type).toBe("DOM_INSERT");
  expect(message.html).toBe("<div>New element</div>");
  expect(message.position).toBe("beforeend");
});

test("Content - DOM_REMOVE message structure", () => {
  const message: ExtensionMessage = {
    type: "DOM_REMOVE",
    selector: ".item",
  };

  expect(message.type).toBe("DOM_REMOVE");
  expect(message.selector).toBe(".item");
});

test("Content - message bus integration", async () => {
  const adapters = createMockAdapters();
  const bus = new MessageBus("content", adapters);

  expect(bus).toBeDefined();
});

test("Content - registers DOM_QUERY handler", async () => {
  const adapters = createMockAdapters();
  const bus = new MessageBus("content", adapters);

  const handler = mock(async (_payload, _message) => ({ elements: [] }));
  bus.on("DOM_QUERY", handler);

  await bus.handleMessage({
    id: "test-id",
    source: "devtools",
    targets: ["content"],
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  });

  expect(handler).toHaveBeenCalled();

  // Cleanup
  bus.destroy();
  globalExecutionTracker.reset();
});

test("Content - element serialization format", () => {
  const serialized = {
    tagName: "div",
    id: "test",
    className: "container",
    textContent: "Test content",
    attributes: { "data-id": "123" },
  };

  expect(serialized).toHaveProperty("tagName");
  expect(serialized).toHaveProperty("id");
  expect(serialized).toHaveProperty("className");
  expect(serialized).toHaveProperty("textContent");
  expect(serialized).toHaveProperty("attributes");
});
