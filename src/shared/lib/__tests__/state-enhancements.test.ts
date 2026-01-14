/**
 * Tests for DX Enhancements #1 and #5
 *
 * Enhancement #1: Verification tracking via .verify property
 * Enhancement #5: Exposed .loaded promise for hydration control
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { $sharedState, $persistedState } from "../state";
import { getMessageBus } from "../message-bus";

describe("Enhancement #1: Verification Tracking (.verify property)", () => {
  beforeEach(() => {
    // Clear any existing state
    if (typeof chrome !== "undefined" && chrome.storage?.local) {
      chrome.storage.local.clear();
    }
  });

  test("should create verification mirror when verify: true", () => {
    const state = $sharedState("test-verify", { count: 0, active: false }, { verify: true });

    expect(state.verify).toBeDefined();
    expect(state.verify).toEqual({ count: 0, active: false });
  });

  test("should not create verification mirror when verify is omitted", () => {
    const state = $sharedState("test-no-verify", { count: 0 });

    expect(state.verify).toBeUndefined();
  });

  test("should synchronize verify mirror when signal value changes", async () => {
    const state = $sharedState("test-sync", { count: 0, name: "test" }, { verify: true });

    // Wait for state to be fully loaded and effect to be set up
    await state.loaded;
    await new Promise((resolve) => setTimeout(resolve, 20));

    expect(state.verify!.count).toBe(0);
    expect(state.verify!.name).toBe("test");

    // Update the signal
    state.value = { count: 5, name: "updated" };

    // Wait for effect to run
    await new Promise((resolve) => setTimeout(resolve, 50));

    // Verify mirror should be updated
    expect(state.verify!.count).toBe(5);
    expect(state.verify!.name).toBe("updated");
  });

  test("should handle nested object updates", async () => {
    const state = $sharedState(
      "test-nested",
      {
        user: { name: "Alice", age: 30 },
        settings: { theme: "dark" },
      },
      { verify: true }
    );

    // Wait for state to be fully loaded and effect to be set up
    await state.loaded;
    await new Promise((resolve) => setTimeout(resolve, 20));

    expect(state.verify!.user.name).toBe("Alice");
    expect(state.verify!.settings.theme).toBe("dark");

    state.value = {
      user: { name: "Bob", age: 25 },
      settings: { theme: "light" },
    };

    await new Promise((resolve) => setTimeout(resolve, 50));

    expect(state.verify!.user.name).toBe("Bob");
    expect(state.verify!.user.age).toBe(25);
    expect(state.verify!.settings.theme).toBe("light");
  });

  test("should handle array updates", async () => {
    const state = $sharedState("test-array", { items: ["a", "b"] }, { verify: true });

    // Wait for state to be fully loaded and effect to be set up
    await state.loaded;
    await new Promise((resolve) => setTimeout(resolve, 20));

    expect(state.verify!.items).toEqual(["a", "b"]);

    state.value = { items: ["a", "b", "c"] };

    await new Promise((resolve) => setTimeout(resolve, 50));

    expect(state.verify!.items).toEqual(["a", "b", "c"]);
  });

  test("should create independent copy (not reference)", async () => {
    const state = $sharedState("test-copy", { data: { count: 0 } }, { verify: true });

    // Wait for state to be fully loaded and effect to be set up
    await state.loaded;
    await new Promise((resolve) => setTimeout(resolve, 20));

    // Mutating the signal value should not affect verify mirror until reassigned
    const original = state.value;
    state.value = { data: { count: 5 } };

    await new Promise((resolve) => setTimeout(resolve, 50));

    // Verify mirror should reflect the new value
    expect(state.verify!.data.count).toBe(5);
    // Original value should still be 0 (immutable pattern)
    expect(original.data.count).toBe(0);
  });
});

describe("Enhancement #5: Exposed .loaded Promise", () => {
  test("$sharedState should expose loaded promise", () => {
    const state = $sharedState("test-loaded", { count: 0 });

    expect(state.loaded).toBeDefined();
    expect(state.loaded).toBeInstanceOf(Promise);
  });

  test("$persistedState should expose loaded promise", () => {
    const state = $persistedState("test-persisted-loaded", { count: 0 });

    expect(state.loaded).toBeDefined();
    expect(state.loaded).toBeInstanceOf(Promise);
  });

  test("loaded promise should resolve after hydration", async () => {
    const state = $sharedState("test-hydration", { count: 0 });

    // Should be able to await the promise
    await expect(state.loaded).resolves.toBeUndefined();

    // After resolution, should be able to safely access value
    expect(state.value).toBeDefined();
  });

  test("multiple awaits on loaded promise should work", async () => {
    const state = $sharedState("test-multiple-awaits", { count: 0 });

    // First await
    await state.loaded;

    // Second await should also work (promise already resolved)
    await state.loaded;

    expect(state.value).toBeDefined();
  });

  test("can use loaded promise to coordinate initialization", async () => {
    const settings = $sharedState("settings-init", { theme: "dark", count: 0 });
    const bookmarks = $sharedState("bookmarks-init", [] as string[]);

    // Wait for both to load
    await Promise.all([settings.loaded, bookmarks.loaded]);

    // Now both are guaranteed to be hydrated
    expect(settings.value).toBeDefined();
    expect(bookmarks.value).toBeDefined();
  });
});

describe("Integration: verify + loaded", () => {
  test("should work together for verification patterns", async () => {
    const loginState = $sharedState(
      "login-integration",
      { loggedIn: false, username: undefined as string | undefined },
      { verify: true }
    );

    // Wait for hydration and effect setup
    await loginState.loaded;
    await new Promise((resolve) => setTimeout(resolve, 20));

    // Verification mirror should be available
    expect(loginState.verify).toBeDefined();
    expect(loginState.verify!.loggedIn).toBe(false);

    // Update state
    loginState.value = { loggedIn: true, username: "alice" };

    await new Promise((resolve) => setTimeout(resolve, 50));

    // Verify mirror should reflect the change
    expect(loginState.verify!.loggedIn).toBe(true);
    expect(loginState.verify!.username).toBe("alice");
  });
});
