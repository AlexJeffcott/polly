/**
 * Full-Featured Example - Message Handlers
 *
 * State and handlers live here so the background entry (index.ts) and the
 * tests both register them on a bus built by createBackground(): the tests
 * cross the same handler boundary the extension does (polly#57).
 */

import { validateShape } from "@fairfox/polly";
import type { MessageBus } from "@fairfox/polly/message-bus";
import { $sharedState } from "@fairfox/polly/state";
import { ensures, requires } from "@fairfox/polly/verify";
import type { AllMessages, Bookmark, Settings } from "../shared/types/messages";

// Application state with automatic persistence and validation
export const settings = $sharedState<Settings>(
  "full-featured-settings",
  {
    theme: "auto",
    autoSync: true,
    debugMode: false,
    notifications: true,
    apiEndpoint: "",
    refreshInterval: 60000,
  },
  {
    // Enhancement #4: Simple shape validation instead of manual type guards
    validator: validateShape<Settings>({
      theme: "string",
      autoSync: "boolean",
      debugMode: "boolean",
      notifications: "boolean",
      apiEndpoint: "string",
      refreshInterval: "number",
    }),
  },
);

export const bookmarks = $sharedState<Bookmark[]>("bookmarks", []);

// Verified numeric state for bookmark count (exercises { type: "number" } verification)
export const bookmarkCount = $sharedState("bookmarkCount", 0, { verify: true });

// Enhancement #1: Unified state with verification tracking
// The .verify property provides a plain object mirror for verification
export const loginState = $sharedState<{
  loggedIn: boolean;
  username?: string;
}>(
  "login-state",
  {
    loggedIn: false,
  },
  { verify: true }, // Enable verification tracking
);

// Enhancement #1: Export verification state - automatically syncs with loginState
if (!loginState.verify) {
  throw new Error(
    "Verification mirror not created - ensure verify: true is set",
  );
}
export const state = loginState.verify;

// State-level constraints are defined in specs/constraints.ts
// They're automatically discovered via transitive import following

/* Enhancement #2: Runtime constraint checking (optional). Uncomment to enable.
 *
 *   import { $constraints } from "@fairfox/polly/verify";
 *   $constraints("loggedIn", {
 *     USER_LOGOUT: {
 *       requires: (s) => s.loggedIn === true,
 *       message: "Must be logged in to logout"
 *     },
 *     BOOKMARK_ADD: {
 *       requires: (s) => s.loggedIn === true,
 *       message: "Must be logged in to add bookmarks"
 *     },
 *     SETTINGS_UPDATE: {
 *       requires: (s) => s.loggedIn === true,
 *       message: "Must be logged in to update settings"
 *     }
 *   }, { runtime: true });
 */

/**
 * Register every handler on a bus.
 */
export function registerHandlers(bus: MessageBus<AllMessages>): void {
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

    // Postcondition - verify login state was updated
    ensures(
      loginState.value.loggedIn === true,
      "User must be logged in after login",
    );

    return {
      success: true,
      user: { username },
    };
  });

  bus.on("USER_LOGOUT", async () => {
    // Precondition: must be logged in to logout
    requires(loginState.value.loggedIn === true, "Must be logged in to logout");

    await bus.adapters.storage.remove(["user"]);

    // Update login state - verification mirror (state) auto-syncs via .verify property
    loginState.value = { loggedIn: false };

    // Postcondition - verify logout state
    ensures(
      loginState.value.loggedIn === false,
      "User must be logged out after logout",
    );

    return { success: true };
  });

  // Bookmark management
  bus.on("BOOKMARK_ADD", async (payload) => {
    // Precondition: must be logged in to add bookmarks
    requires(
      loginState.value.loggedIn === true,
      "Must be logged in to add bookmarks",
    );

    const { url, title } = payload;

    const bookmark: Bookmark = {
      id: crypto.randomUUID(),
      url,
      title,
      timestamp: Date.now(),
    };

    const current = bookmarks.value || [];
    bookmarks.value = [...current, bookmark];
    // Same value as bookmarks.value.length, in a form the TLA+ extractor can
    // translate (`@ + 1`): `bookmarks` is not a verified field, so a write
    // derived from its length is dropped from the model and this handler's
    // ensures fails.
    bookmarkCount.value++;
    // $sharedState automatically persists to storage

    ensures(
      bookmarkCount.value > 0,
      "Bookmark count must be positive after add",
    );

    return { success: true, bookmark };
  });

  bus.on("BOOKMARK_REMOVE", async (payload) => {
    const { id } = payload;

    const current = bookmarks.value || [];
    bookmarks.value = current.filter((b) => b.id !== id);
    bookmarkCount.value = bookmarks.value.length;
    // $sharedState automatically persists to storage

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
    requires(
      loginState.value.loggedIn === true,
      "Must be logged in to update settings",
    );

    const { type, ...updates } = payload;
    settings.value = { ...settings.value, ...updates };
    // $sharedState automatically persists to storage

    return { success: true, settings: settings.value };
  });

  bus.on("GET_SETTINGS", async () => {
    return { success: true, settings: settings.value };
  });

  bus.on("GET_BOOKMARKS", async () => {
    return { success: true, bookmarks: bookmarks.value };
  });
}
