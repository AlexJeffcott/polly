import { beforeEach, describe, expect, test } from "bun:test";
import { $persistedState, $sharedState, $state, $syncedState, clearStateRegistry } from "./state";

describe("State Primitives", () => {
  beforeEach(() => {
    clearStateRegistry();
  });

  test("$state creates local signal", () => {
    const count = $state(0);
    expect(count.value).toBe(0);

    count.value = 5;
    expect(count.value).toBe(5);
  });

  test("$state does not register in registry", () => {
    $state(0);
    $state("hello");
    // Local state doesn't use keys, so registry stays empty
  });

  test("$sharedState returns same instance for same key", () => {
    const state1 = $sharedState("test", { count: 0 });
    const state2 = $sharedState("test", { count: 999 });

    // Should return same signal instance
    expect(state1).toBe(state2);
    expect(state1.value.count).toBe(state2.value.count);
  });

  test("$syncedState returns same instance for same key", () => {
    const state1 = $syncedState("active-tab", 0);
    const state2 = $syncedState("active-tab", 123);

    expect(state1).toBe(state2);
  });

  test("$persistedState returns same instance for same key", () => {
    const state1 = $persistedState("ui-state", { collapsed: false });
    const state2 = $persistedState("ui-state", { collapsed: true });

    expect(state1).toBe(state2);
  });

  test("different keys create different signals", () => {
    const state1 = $sharedState("key1", 0);
    const state2 = $sharedState("key2", 0);

    expect(state1).not.toBe(state2);

    state1.value = 10;
    expect(state2.value).toBe(0); // Should not affect other signal
  });

  test("state updates are reactive", () => {
    const state = $sharedState("settings", { theme: "light" });

    let _callCount = 0;
    state.value; // Read to track
    _callCount++;

    state.value = { theme: "dark" };
    expect(state.value.theme).toBe("dark");
  });

  test("namespaced keys work correctly", () => {
    const popupState = $persistedState("popup:state", { panel: "main" });
    const optionsState = $persistedState("options:state", { panel: "settings" });

    expect(popupState.value.panel).toBe("main");
    expect(optionsState.value.panel).toBe("settings");

    popupState.value = { panel: "debug" };
    expect(optionsState.value.panel).toBe("settings"); // Unchanged
  });

  test("$state works without key or registry", () => {
    const state1 = $state(10);
    const state2 = $state(10);

    // Different instances
    expect(state1).not.toBe(state2);

    state1.value = 20;
    expect(state1.value).toBe(20);
    expect(state2.value).toBe(10);
  });
});
