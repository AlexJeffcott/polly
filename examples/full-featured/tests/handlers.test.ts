/**
 * Tests for Full-Featured Extension Handlers
 *
 * Drives the real handlers through a createBackground() bus with mock adapters,
 * the same path the extension entry (src/background/index.ts) takes.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import { createBackground, MessageRouter } from "@fairfox/polly/background";
import type { MessageBus } from "@fairfox/polly/message-bus";
import { createMockAdapters, type MockExtensionAdapters } from "@fairfox/polly/test";
import {
  bookmarkCount,
  bookmarks,
  loginState,
  registerHandlers,
  settings,
  state,
} from "../src/background/handlers";
import type { AllMessages, Bookmark, Settings, User } from "../src/shared/types/messages";

type Response<T = unknown> = { success: boolean; data?: T; error?: string };

function send<T = unknown>(bus: MessageBus<AllMessages>, payload: AllMessages): Promise<Response<T>> {
  return bus.handleMessage({
    id: crypto.randomUUID(),
    source: "popup",
    targets: ["background"],
    timestamp: Date.now(),
    payload,
  }) as Promise<Response<T>>;
}

const DEFAULT_SETTINGS: Settings = {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: "",
  refreshInterval: 60000,
};

// Read the module's own initial values before any hook resets them.
test("starts logged out with no bookmarks and default settings", () => {
  expect(loginState.value).toEqual({ loggedIn: false });
  expect(state.loggedIn).toBe(false);
  expect(bookmarks.value).toEqual([]);
  expect(bookmarkCount.value).toBe(0);
  expect(settings.value).toEqual(DEFAULT_SETTINGS);
});

let bus: MessageBus<AllMessages>;
let adapters: MockExtensionAdapters;

// A file-level beforeEach would also run before the initial-state test above,
// so the reset hook lives inside this describe.
describe("handlers on a createBackground() bus", () => {
beforeEach(() => {
  MessageRouter.resetInstance();
  adapters = createMockAdapters();
  bus = createBackground<AllMessages>(createMockAdapters());
  // Cold start: every signal back to its initial value
  loginState.value = { loggedIn: false };
  bookmarks.value = [];
  bookmarkCount.value = 0;
  settings.value = { ...DEFAULT_SETTINGS };
  registerHandlers(bus);
});

async function login(username = "testuser") {
  const response = await send<{ success: boolean; user: { username: string } }>(bus, {
    type: "USER_LOGIN",
    username,
    token: "test-token",
  });
  expect(response.success).toBe(true);
  return response;
}

describe("USER_LOGIN", () => {
  test("stores the user and flips the login state", async () => {
    const response = await login("alice");

    expect(response.data).toEqual({ success: true, user: { username: "alice" } });
    expect(loginState.value).toEqual({ loggedIn: true, username: "alice" });
    expect(state.loggedIn).toBe(true);

    const stored = await bus.adapters.storage.get<{ user: User }>("user");
    expect(stored.user.username).toBe("alice");
    expect(stored.user.token).toBe("test-token");
    expect(typeof stored.user.loginTime).toBe("number");
  });
});

describe("USER_LOGOUT", () => {
  test("clears the stored user and the login state", async () => {
    await login();

    const response = await send(bus, { type: "USER_LOGOUT" });

    expect(response.success).toBe(true);
    expect(response.data).toEqual({ success: true });
    expect(loginState.value).toEqual({ loggedIn: false });
    const stored = await bus.adapters.storage.get<{ user?: User }>("user");
    expect(stored.user).toBeUndefined();
  });
});

describe("BOOKMARK_ADD", () => {
  test("appends a bookmark and counts it", async () => {
    await login();

    const response = await send<{ success: boolean; bookmark: Bookmark }>(bus, {
      type: "BOOKMARK_ADD",
      url: "https://example.com",
      title: "Example",
    });

    expect(response.success).toBe(true);
    const bookmark = response.data?.bookmark as Bookmark;
    expect(bookmark.url).toBe("https://example.com");
    expect(bookmark.title).toBe("Example");
    expect(typeof bookmark.id).toBe("string");
    expect(typeof bookmark.timestamp).toBe("number");
    expect(bookmarks.value).toEqual([bookmark]);
    expect(bookmarkCount.value).toBe(1);
  });

  test("keeps earlier bookmarks", async () => {
    await login();
    await send(bus, { type: "BOOKMARK_ADD", url: "https://a.test", title: "A" });
    await send(bus, { type: "BOOKMARK_ADD", url: "https://b.test", title: "B" });

    expect(bookmarks.value.map((b) => b.title)).toEqual(["A", "B"]);
    expect(bookmarkCount.value).toBe(2);
  });
});

describe("BOOKMARK_REMOVE", () => {
  test("removes only the bookmark with that id", async () => {
    await login();
    const a = await send<{ bookmark: Bookmark }>(bus, {
      type: "BOOKMARK_ADD",
      url: "https://a.test",
      title: "A",
    });
    await send(bus, { type: "BOOKMARK_ADD", url: "https://b.test", title: "B" });

    const response = await send(bus, { type: "BOOKMARK_REMOVE", id: a.data?.bookmark.id ?? "" });

    expect(response.success).toBe(true);
    expect(response.data).toEqual({ success: true });
    expect(bookmarks.value.map((b) => b.title)).toEqual(["B"]);
    expect(bookmarkCount.value).toBe(1);
  });

  test("leaves the list unchanged for an unknown id", async () => {
    await login();
    await send(bus, { type: "BOOKMARK_ADD", url: "https://a.test", title: "A" });

    await send(bus, { type: "BOOKMARK_REMOVE", id: "missing" });

    expect(bookmarks.value).toHaveLength(1);
    expect(bookmarkCount.value).toBe(1);
  });
});

describe("GET_BOOKMARKS", () => {
  test("returns the current list", async () => {
    await login();
    await send(bus, { type: "BOOKMARK_ADD", url: "https://a.test", title: "A" });

    const response = await send(bus, { type: "GET_BOOKMARKS" });

    expect(response.data).toEqual({ success: true, bookmarks: bookmarks.value });
  });
});

describe("TAB_GET_CURRENT", () => {
  test("returns the active tab", async () => {
    const tab = { id: 7, active: true, url: "https://tab.test" } as chrome.tabs.Tab;
    bus.adapters.tabs.query = async (queryInfo) => {
      expect(queryInfo).toEqual({ active: true, currentWindow: true });
      return [tab];
    };

    const response = await send(bus, { type: "TAB_GET_CURRENT" });

    expect(response.success).toBe(true);
    expect(response.data).toEqual({ tab });
  });

  test("fails when no tab is active", async () => {
    bus.adapters.tabs.query = async () => [];

    const response = await send(bus, { type: "TAB_GET_CURRENT" });

    expect(response.success).toBe(false);
    expect(response.error).toBe("No active tab found");
  });
});

describe("TAB_OPEN", () => {
  test("creates a tab at the url", async () => {
    const response = await send(bus, { type: "TAB_OPEN", url: "https://open.test" });

    expect(response.data).toEqual({ success: true });
    const tabs = await bus.adapters.tabs.query({});
    expect(tabs.map((t) => t.url)).toEqual(["https://open.test"]);
  });
});

describe("SETTINGS_UPDATE", () => {
  test("merges the update into the settings", async () => {
    await login();

    const response = await send<{ success: boolean; settings: Settings }>(bus, {
      type: "SETTINGS_UPDATE",
      theme: "dark",
      refreshInterval: 1000,
    });

    const expected: Settings = { ...DEFAULT_SETTINGS, theme: "dark", refreshInterval: 1000 };
    expect(response.data).toEqual({ success: true, settings: expected });
    expect(settings.value).toEqual(expected);
  });

  test("does not store the message type as a setting", async () => {
    await login();

    await send(bus, { type: "SETTINGS_UPDATE", debugMode: true });

    expect("type" in settings.value).toBe(false);
    expect(settings.value.debugMode).toBe(true);
  });
});

describe("GET_SETTINGS", () => {
  test("returns the current settings", async () => {
    const response = await send(bus, { type: "GET_SETTINGS" });

    expect(response.data).toEqual({ success: true, settings: DEFAULT_SETTINGS });
  });
});

describe("mock adapters are independent per bus", () => {
  test("a second adapter set sees none of the bus storage", async () => {
    await login();

    const stored = await adapters.storage.get<{ user?: User }>("user");
    expect(stored.user).toBeUndefined();
  });
});
});
