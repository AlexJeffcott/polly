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
import { validateShape } from "@fairfox/polly";
import type { AllMessages, Bookmark, Settings } from "../shared/types/messages";
// Import verification constraints (discovered via transitive import following)
import "../../specs/constraints.js";

// Application state with automatic persistence and validation
const settings = $sharedState<Settings>("app-settings", {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: "",
  refreshInterval: 60000,
}, {
  // Enhancement #4: Simple shape validation instead of manual type guards
  validator: validateShape<Settings>({
    theme: 'string',
    autoSync: 'boolean',
    debugMode: 'boolean',
    notifications: 'boolean',
    apiEndpoint: 'string',
    refreshInterval: 'number'
  })
});

const bookmarks = $sharedState<Bookmark[]>("bookmarks", []);

// Enhancement #1: Unified state with verification tracking
// The .verify property provides a plain object mirror for verification
const loginState = $sharedState<{ loggedIn: boolean; username?: string }>(
  "login-state",
  {
    loggedIn: false,
  },
  { verify: true } // Enable verification tracking
);

// Enhancement #1: Export verification state - automatically syncs with loginState
export const state = loginState.verify!;

// Note: State-level constraints are defined in specs/constraints.ts
// They're automatically discovered via transitive import following

// Enhancement #2: Runtime constraint checking (optional)
// Uncomment to enable runtime enforcement:
// import { $constraints } from "@fairfox/polly/verify";
// $constraints("loggedIn", {
//   USER_LOGOUT: {
//     requires: (s) => s.loggedIn === true,
//     message: "Must be logged in to logout"
//   },
//   BOOKMARK_ADD: {
//     requires: (s) => s.loggedIn === true,
//     message: "Must be logged in to add bookmarks"
//   },
//   SETTINGS_UPDATE: {
//     requires: (s) => s.loggedIn === true,
//     message: "Must be logged in to update settings"
//   }
// }, { runtime: true });

// Initialize background script
const bus = getMessageBus<AllMessages>("background");
new MessageRouter(bus);

// Enhancement #2: Register state accessor for runtime constraint checking
// This allows constraints to access current state when checking preconditions
bus.setStateAccessor(() => state);

// User authentication
bus.on("USER_LOGIN", async (payload) => {
  const { username, token } = payload;

  // Simulate authentication
  await bus.adapters.storage.set({
    user: { username, token, loginTime: Date.now() },
  });

  // Update login state - verification mirror (state) auto-syncs via .verify property
  loginState.value = { loggedIn: true, username };

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

  // Update login state - verification mirror (state) auto-syncs via .verify property
  loginState.value = { loggedIn: false };

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
  // Note: $sharedState automatically persists to storage

  return { success: true, bookmark };
});

bus.on("BOOKMARK_REMOVE", async (payload) => {
  const { id } = payload;

  const current = bookmarks.value || [];
  bookmarks.value = current.filter((b) => b.id !== id);
  // Note: $sharedState automatically persists to storage

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
  // Note: $sharedState automatically persists to storage

  return { success: true, settings: settings.value };
});

bus.on("GET_SETTINGS", async () => {
  return { success: true, settings: settings.value };
});

bus.on("GET_BOOKMARKS", async () => {
  return { success: true, bookmarks: bookmarks.value };
});

// Initialize - wait for state to load from storage
// Note: $sharedState automatically loads from storage in the background
// We only need to wait for completion if we need the loaded values immediately
(async () => {
  // Wait for state hydration to complete
  await settings.loaded;
  await bookmarks.loaded;

  console.log("[Full-Featured Extension] Background initialized");
})();
