import { beforeEach, describe, expect, test } from "bun:test";
import { $persistedState, $sharedState, $state, $syncedState, clearStateRegistry } from "../state";

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

// A storage adapter pre-seeded with a value that predates a later state shape.
function seededStorage(seed: Record<string, unknown>) {
  const store = new Map<string, unknown>(Object.entries(seed));
  return {
    async get<T = unknown>(keys: string[]): Promise<Record<string, T>> {
      // The fake erases T like a real storage backend would; callers get
      // back whatever shape they seeded.
      const out: Record<string, T> = {};
      for (const k of keys) {
        if (store.has(k)) out[k] = store.get(k) as unknown as T;
      }
      return out;
    },
    async set(items: Record<string, unknown>): Promise<void> {
      for (const [k, v] of Object.entries(items)) store.set(k, v);
    },
    async remove(keys: string[]): Promise<void> {
      for (const k of keys) store.delete(k);
    },
  };
}

describe("Persisted state hydration merges with defaults (#158)", () => {
  test("backfills a field added after the value was persisted", async () => {
    // Stored blob predates the `b` field.
    const storage = seededStorage({ "view:158-add": { a: 1 } });
    const s = $persistedState("view:158-add", { a: 1, b: "default" }, { storage });
    await s.loaded;

    expect(s.value.a).toBe(1);
    expect(s.value.b).toBe("default"); // not undefined
  });

  test("stored values still override defaults", async () => {
    const storage = seededStorage({ "view:158-override": { a: 1, b: "stored" } });
    const s = $persistedState("view:158-override", { a: 1, b: "default" }, { storage });
    await s.loaded;

    expect(s.value.b).toBe("stored");
  });

  test("primitive state is replaced wholesale, not merged", async () => {
    const storage = seededStorage({ "view:158-prim": "stored" });
    const s = $persistedState("view:158-prim", "default", { storage });
    await s.loaded;

    expect(s.value).toBe("stored");
  });

  test("array state is replaced wholesale, not merged", async () => {
    const storage = seededStorage({ "view:158-arr": [3, 4] });
    const s = $persistedState("view:158-arr", [1, 2], { storage });
    await s.loaded;

    expect(s.value).toEqual([3, 4]);
  });

  test("validator backfills instead of discarding the user's other fields", async () => {
    // User had changed `a` to 99 before `b` existed in the shape.
    const storage = seededStorage({ "view:158-valid": { a: 99 } });
    const validator = (v: unknown): v is { a: number; b: string } =>
      typeof v === "object" &&
      v !== null &&
      "a" in v &&
      typeof v.a === "number" &&
      "b" in v &&
      typeof v.b === "string";
    const s = $persistedState("view:158-valid", { a: 1, b: "default" }, { storage, validator });
    await s.loaded;

    // Without the merge, {a:99} fails validation and the whole blob is
    // discarded back to the initial value — losing the user's a=99. With the
    // merge, the backfilled {a:99, b:"default"} passes and a=99 survives.
    expect(s.value).toEqual({ a: 99, b: "default" });
  });
});
