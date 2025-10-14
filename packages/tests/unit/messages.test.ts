import { expect, test } from "bun:test";
import { ALL_CONTEXTS, type ExtensionMessage, type MessageResponse } from "@/shared/types/messages";
import { createMockRoutedMessage, expectType } from "../helpers/test-utils";

test("ExtensionMessage - DOM_QUERY type safety", () => {
  const message: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  expect(message.type).toBe("DOM_QUERY");
  expect(message.selector).toBe(".test");

  // @ts-expect-error - should not have endpoint property
  expectType<undefined>(message.endpoint);
});

test("ExtensionMessage - API_REQUEST type safety", () => {
  const message: ExtensionMessage = {
    type: "API_REQUEST",
    endpoint: "/api/test",
    method: "GET",
  };

  expect(message.type).toBe("API_REQUEST");
  expect(message.endpoint).toBe("/api/test");
  expect(message.method).toBe("GET");
});

test("MessageResponse - type inference from DOM_QUERY", () => {
  type QueryMessage = Extract<ExtensionMessage, { type: "DOM_QUERY" }>;
  type QueryResponse = MessageResponse<QueryMessage>;

  const response: QueryResponse = {
    elements: [
      {
        tag: "div",
        text: "Test",
        html: "<div>Test</div>",
        attrs: {},
      },
    ],
  };

  expect(response.elements).toBeArray();
  expect(response.elements[0]?.tag).toBe("div");
});

test("MessageResponse - type inference from API_REQUEST", () => {
  type ApiMessage = Extract<ExtensionMessage, { type: "API_REQUEST" }>;
  type ApiResponse = MessageResponse<ApiMessage>;

  const response: ApiResponse = {
    data: { test: true },
    status: 200,
    statusText: "OK",
    headers: {},
  };

  expect(response.status).toBe(200);
  expect(response.data).toEqual({ test: true });
});

test("MessageResponse - type inference from CLIPBOARD_WRITE", () => {
  type ClipboardMessage = Extract<ExtensionMessage, { type: "CLIPBOARD_WRITE" }>;
  type ClipboardResponse = MessageResponse<ClipboardMessage>;

  const response: ClipboardResponse = {
    success: true,
  };

  expect(response.success).toBe(true);
});

test("RoutedMessage - wraps ExtensionMessage with metadata", () => {
  const payload: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  const routed = createMockRoutedMessage(payload, {
    source: "content",
    targets: ["background"],
    tabId: 123,
  });

  expect(routed.id).toBeString();
  expect(routed.source).toBe("content");
  expect(routed.targets).toEqual(["background"]);
  expect(routed.tabId).toBe(123);
  expect(routed.timestamp).toBeNumber();
  expect(routed.payload).toEqual(payload);
});

test("RoutedMessage - broadcast target", () => {
  const payload: ExtensionMessage = {
    type: "STATE_SYNC",
    key: "test-state",
    value: { count: 1 },
    clock: 1,
  };

  const routed = createMockRoutedMessage(payload, {
    targets: ALL_CONTEXTS,
  });

  expect(routed.targets).toEqual(ALL_CONTEXTS);
});

test("ExtensionMessage - discriminated union exhaustiveness", () => {
  const messages: ExtensionMessage[] = [
    { type: "DOM_QUERY", selector: ".test" },
    { type: "API_REQUEST", endpoint: "/api", method: "GET" },
    { type: "CLIPBOARD_WRITE", text: "test" },
    { type: "STATE_SYNC", key: "test", value: {}, clock: 1 },
    { type: "LOG", level: "info", message: "test", source: "background", timestamp: Date.now() },
  ];

  for (const message of messages) {
    expect(message.type).toBeString();
    expect(message).toHaveProperty("type");
  }
});

test("ExtensionMessage - STATE_SYNC with value", () => {
  const message: ExtensionMessage = {
    type: "STATE_SYNC",
    key: "settings",
    value: {
      debugMode: true,
    },
    clock: 1,
  };

  expect(message.type).toBe("STATE_SYNC");
  expect(message.value).toEqual({ debugMode: true });
});

test("ExtensionMessage - PAGE_CALL_FN with arguments", () => {
  const message: ExtensionMessage = {
    type: "PAGE_CALL_FN",
    fnName: "testFunction",
    args: [1, "test", { key: "value" }],
  };

  expect(message.type).toBe("PAGE_CALL_FN");
  if (message.type === "PAGE_CALL_FN") {
    expect(message.fnName).toBe("testFunction");
    expect(message.args).toEqual([1, "test", { key: "value" }]);
  }
});

test("ExtensionMessage - CONTEXT_MENU_CLICKED", () => {
  const message: ExtensionMessage = {
    type: "CONTEXT_MENU_CLICKED",
    menuId: "test-menu",
    info: {
      menuItemId: "test-menu",
      pageUrl: "https://example.com",
      selectionText: "selected text",
    } as chrome.contextMenus.OnClickData,
    tabId: 1,
  };

  expect(message.type).toBe("CONTEXT_MENU_CLICKED");
  if (message.type === "CONTEXT_MENU_CLICKED") {
    expect(message.menuId).toBe("test-menu");
    expect(message.info.pageUrl).toBe("https://example.com");
    expect(message.info.selectionText).toBe("selected text");
  }
});
