/**
 * Full-Featured Example - Background Script
 *
 * Demonstrates real-world extension patterns using the framework:
 * - State management with signals
 * - Chrome API usage through adapters
 * - Message routing between contexts
 * - Data persistence
 */

import { getMessageBus } from "@fairfox/polly/message-bus";
import { MessageRouter } from "@fairfox/polly/message-router";
import { $sharedState } from "@fairfox/polly/state";
import { $constraints } from "@fairfox/polly/verify";
import type { AllMessages, Bookmark, Settings } from "../shared/types/messages";

// Application state
const settings = $sharedState<Settings>("app-settings", {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: "",
  refreshInterval: 60000,
});

const bookmarks = $sharedState<Bookmark[]>("bookmarks", []);

// Login state tracking (for UI/persistence)
const loginState = $sharedState<{ loggedIn: boolean; username?: string }>("login-state", {
  loggedIn: false,
});

// State object for verification (code analysis detects direct assignments)
const state = {
  loggedIn: false,
};

// State-level constraints (declarative, automatically wired to handlers)
$constraints("loggedIn", {
  USER_LOGOUT: {
    requires: "state.loggedIn === true",
    message: "Must be logged in to logout",
  },
  BOOKMARK_ADD: {
    requires: "state.loggedIn === true",
    message: "Must be logged in to add bookmarks",
  },
  SETTINGS_UPDATE: {
    requires: "state.loggedIn === true",
    message: "Must be logged in to update settings",
  },
});

// Type guards for storage validation
function isSettings(value: unknown): value is Settings {
  return (
    value !== null &&
    typeof value === "object" &&
    "theme" in value &&
    "autoSync" in value &&
    "debugMode" in value &&
    "notifications" in value &&
    "apiEndpoint" in value &&
    "refreshInterval" in value
  );
}

function isBookmarkArray(value: unknown): value is Bookmark[] {
  return Array.isArray(value);
}

// Initialize background script
const bus = getMessageBus<AllMessages>("background");
new MessageRouter(bus);

// User authentication
bus.on("USER_LOGIN", async (payload) => {
  const { username, token } = payload;

  // Simulate authentication
  await bus.adapters.storage.set({
    user: { username, token, loginTime: Date.now() },
  });

  // Update login state (for UI/persistence and verification)
  loginState.value = { loggedIn: true, username };
  state.loggedIn = true;

  return {
    success: true,
    user: { username },
  };
});

bus.on("USER_LOGOUT", async () => {
  // Precondition: must be logged in to logout
  if (!loginState.value.loggedIn) {
    throw new Error("Cannot logout - not logged in");
  }

  await bus.adapters.storage.remove(["user"]);

  // Update login state (for UI/persistence and verification)
  loginState.value = { loggedIn: false };
  state.loggedIn = false;

  return { success: true };
});

// Bookmark management
bus.on("BOOKMARK_ADD", async (payload) => {
  // Precondition: must be logged in to add bookmarks
  if (!loginState.value.loggedIn) {
    throw new Error("Cannot add bookmark - not logged in");
  }

  const { url, title } = payload;

  const bookmark: Bookmark = {
    id: crypto.randomUUID(),
    url,
    title,
    timestamp: Date.now(),
  };

  const current = bookmarks.value || [];
  bookmarks.value = [...current, bookmark];

  await bus.adapters.storage.set({ bookmarks: bookmarks.value });

  return { success: true, bookmark };
});

bus.on("BOOKMARK_REMOVE", async (payload) => {
  const { id } = payload;

  const current = bookmarks.value || [];
  bookmarks.value = current.filter((b) => b.id !== id);

  await bus.adapters.storage.set({ bookmarks: bookmarks.value });

  return { success: true };
});

// Tab management
bus.on("TAB_GET_CURRENT", async () => {
  const tabs = await bus.adapters.tabs.query({
    active: true,
    currentWindow: true,
  });
  const currentTab = tabs[0];

  if (!currentTab) {
    throw new Error("No active tab found");
  }

  return {
    tab: currentTab,
  };
});

bus.on("TAB_OPEN", async (payload) => {
  const { url } = payload;

  await bus.adapters.tabs.create({ url });

  return { success: true };
});

// Settings management
bus.on("SETTINGS_UPDATE", async (payload) => {
  // Precondition: must be logged in to update settings
  if (!loginState.value.loggedIn) {
    throw new Error("Cannot update settings - not logged in");
  }

  const { type, ...updates } = payload;
  settings.value = { ...settings.value, ...updates };

  await bus.adapters.storage.set({ settings: settings.value });

  return { success: true, settings: settings.value };
});

bus.on("GET_SETTINGS", async () => {
  return { success: true, settings: settings.value };
});

bus.on("GET_BOOKMARKS", async () => {
  return { success: true, bookmarks: bookmarks.value };
});

// Initialize state from storage
(async () => {
  const stored = await bus.adapters.storage.get(["settings", "bookmarks"]);

  if (isSettings(stored.settings)) {
    settings.value = stored.settings;
  }

  if (isBookmarkArray(stored.bookmarks)) {
    bookmarks.value = stored.bookmarks;
  }

  console.log("[Full-Featured Extension] Background initialized");
})();
