/**
 * Tests for Full-Featured Extension Handlers
 *
 * Demonstrates comprehensive testing with @fairfox/polly/test
 */

import { beforeEach, describe, expect, test } from "bun:test";
import { type MockExtensionAdapters, createMockAdapters } from "@fairfox/polly/test";
import type { Bookmark, Settings, User } from "../src/shared/types/messages";

describe("User Authentication Logic", () => {
  let adapters: MockExtensionAdapters;

  beforeEach(() => {
    adapters = createMockAdapters();
  });

  test("user can login", async () => {
    // Simulate USER_LOGIN handler logic
    const loginHandler = async (username: string, token: string) => {
      await adapters.storage.set({
        user: { username, token, loginTime: Date.now() },
      });

      return {
        success: true,
        user: { username },
      };
    };

    const response = await loginHandler("testuser", "test-token");

    expect(response.success).toBe(true);
    expect(response.user.username).toBe("testuser");

    // Verify storage was updated
    const stored = await adapters.storage.get<{ user: User }>("user");
    expect(stored.user).toBeDefined();
    expect(stored.user.username).toBe("testuser");
  });

  test("user can logout", async () => {
    // Setup: login first
    await adapters.storage.set({
      user: { username: "testuser", token: "test-token", loginTime: Date.now() },
    });

    // Simulate USER_LOGOUT handler logic
    const logoutHandler = async () => {
      await adapters.storage.remove(["user"]);
      return { success: true };
    };

    const response = await logoutHandler();

    expect(response.success).toBe(true);

    // Verify storage was cleared
    const stored = await adapters.storage.get("user");
    expect(stored.user).toBeUndefined();
  });
});

describe("Bookmark Management Logic", () => {
  let adapters: MockExtensionAdapters;
  let bookmarks: Bookmark[];

  beforeEach(() => {
    adapters = createMockAdapters();
    bookmarks = [];
  });

  test("can add a bookmark", async () => {
    // Simulate BOOKMARK_ADD handler logic
    const addHandler = async (url: string, title: string) => {
      const bookmark: Bookmark = {
        id: crypto.randomUUID(),
        url,
        title,
        timestamp: Date.now(),
      };

      bookmarks = [...bookmarks, bookmark];
      await adapters.storage.set({ bookmarks });

      return { success: true, bookmark };
    };

    const response = await addHandler("https://example.com", "Example Site");

    expect(response.success).toBe(true);
    expect(response.bookmark).toBeDefined();
    expect(response.bookmark.url).toBe("https://example.com");
    expect(response.bookmark.title).toBe("Example Site");

    // Verify storage
    const stored = await adapters.storage.get("bookmarks");
    expect(stored.bookmarks).toHaveLength(1);
  });

  test("can remove a bookmark", async () => {
    // Setup: add a bookmark first
    const bookmark: Bookmark = {
      id: "test-id",
      url: "https://example.com",
      title: "Example",
      timestamp: Date.now(),
    };
    bookmarks = [bookmark];
    await adapters.storage.set({ bookmarks });

    // Simulate BOOKMARK_REMOVE handler logic
    const removeHandler = async (id: string) => {
      bookmarks = bookmarks.filter((b) => b.id !== id);
      await adapters.storage.set({ bookmarks });
      return { success: true };
    };

    const response = await removeHandler("test-id");

    expect(response.success).toBe(true);
    expect(bookmarks).toHaveLength(0);
  });

  test("can get all bookmarks", async () => {
    // Setup: add bookmarks
    bookmarks = [
      {
        id: "1",
        url: "https://example1.com",
        title: "Example 1",
        timestamp: Date.now(),
      },
      {
        id: "2",
        url: "https://example2.com",
        title: "Example 2",
        timestamp: Date.now(),
      },
    ];

    // Simulate GET_BOOKMARKS handler logic
    const getHandler = async () => {
      return { success: true, bookmarks };
    };

    const response = await getHandler();

    expect(response.success).toBe(true);
    expect(response.bookmarks).toHaveLength(2);
  });
});

describe("Settings Management Logic", () => {
  let adapters: MockExtensionAdapters;
  let settings: {
    theme: string;
    autoSync: boolean;
    debugMode: boolean;
    notifications: boolean;
    apiEndpoint: string;
    refreshInterval: number;
  };

  beforeEach(() => {
    adapters = createMockAdapters();

    settings = {
      theme: "auto",
      autoSync: true,
      debugMode: false,
      notifications: true,
      apiEndpoint: "",
      refreshInterval: 60000,
    };
  });

  test("can update settings", async () => {
    // Simulate SETTINGS_UPDATE handler logic
    const updateHandler = async (updates: Partial<typeof settings>) => {
      settings = { ...settings, ...updates };
      await adapters.storage.set({ settings });

      return { success: true, settings };
    };

    const response = await updateHandler({
      theme: "dark",
      debugMode: true,
    });

    expect(response.success).toBe(true);
    expect(response.settings.theme).toBe("dark");
    expect(response.settings.debugMode).toBe(true);

    // Verify storage
    const stored = await adapters.storage.get<{ settings: Settings }>("settings");
    expect(stored.settings.theme).toBe("dark");
  });

  test("can get settings", async () => {
    // Simulate GET_SETTINGS handler logic
    const getHandler = async () => {
      return { success: true, settings };
    };

    const response = await getHandler();

    expect(response.success).toBe(true);
    expect(response.settings).toBeDefined();
    expect(response.settings.theme).toBe("auto");
  });
});

describe("Mock Adapters", () => {
  let adapters: MockExtensionAdapters;

  beforeEach(() => {
    adapters = createMockAdapters();
  });

  test("can use mock tabs adapter", async () => {
    // Create a mock tab
    const mockTab: chrome.tabs.Tab = {
      id: 1,
      url: "https://example.com",
      title: "Example",
      active: true,
      windowId: 1,
      index: 0,
      highlighted: true,
      incognito: false,
      pinned: false,
      selected: true,
      frozen: false,
      discarded: false,
      autoDiscardable: true,
      groupId: -1,
    };

    adapters.tabs._tabs.set(1, mockTab);

    // Query for active tabs
    const tabs = await adapters.tabs.query({ active: true });
    expect(tabs).toHaveLength(1);
    expect(tabs[0].url).toBe("https://example.com");
  });

  test("can use mock storage adapter", async () => {
    await adapters.storage.set({ testKey: "testValue" });

    const result = await adapters.storage.get("testKey");
    expect(result.testKey).toBe("testValue");
  });
});
