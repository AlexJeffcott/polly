import { afterEach, describe, expect, test } from "bun:test";
import { $syncedState, clearStateRegistry, deepEqual } from "@/shared/lib/state";
import type { StateSyncMessage, SyncAdapter } from "@/shared/lib/sync-adapter";

afterEach(() => {
  clearStateRegistry();
});

describe("deepEqual", () => {
  test("returns true for primitives that are equal", () => {
    expect(deepEqual(1, 1)).toBe(true);
    expect(deepEqual("a", "a")).toBe(true);
    expect(deepEqual(true, true)).toBe(true);
    expect(deepEqual(null, null)).toBe(true);
    expect(deepEqual(undefined, undefined)).toBe(true);
  });

  test("returns false for primitives that differ", () => {
    expect(deepEqual(1, 2)).toBe(false);
    expect(deepEqual("a", "b")).toBe(false);
    expect(deepEqual(true, false)).toBe(false);
  });

  test("returns false for null vs object", () => {
    expect(deepEqual(null, {})).toBe(false);
    expect(deepEqual({}, null)).toBe(false);
  });

  test("returns false for undefined vs null", () => {
    expect(deepEqual(undefined, null)).toBe(false);
  });

  test("returns true for structurally equal objects", () => {
    expect(deepEqual({ a: 1, b: "x" }, { a: 1, b: "x" })).toBe(true);
  });

  test("returns false on key-count mismatch", () => {
    expect(deepEqual({ a: 1 }, { a: 1, b: 2 })).toBe(false);
    expect(deepEqual({ a: 1, b: 2 }, { a: 1 })).toBe(false);
  });

  test("returns false for objects with same key count but different keys", () => {
    // Canary for the "missing-key tolerated" mutation. Without the explicit
    // `keysB.includes(key)` check returning false, this would erroneously
    // pass because both objects pass the keysA.length === keysB.length gate.
    expect(deepEqual({ a: 1, b: 2 }, { a: 1, c: 3 })).toBe(false);
  });

  test("returns true for nested equal structures", () => {
    expect(deepEqual({ a: { b: [1, 2] } }, { a: { b: [1, 2] } })).toBe(true);
  });

  test("returns false for nested differences", () => {
    expect(deepEqual({ a: { b: [1, 2] } }, { a: { b: [1, 3] } })).toBe(false);
  });
});

// ─── Lamport-clock boundary ────────────────────────────────────────────────

interface CapturedSyncAdapter extends SyncAdapter {
  /** Manually deliver a message as though it arrived from another context. */
  deliver: (message: StateSyncMessage<unknown>) => void;
  /** Whatever the local effect broadcast (we don't loop it back). */
  broadcasts: Array<StateSyncMessage<unknown>>;
}

function makeCapturedSyncAdapter(): CapturedSyncAdapter {
  const listeners: Array<(message: StateSyncMessage<unknown>) => void> = [];
  const broadcasts: Array<StateSyncMessage<unknown>> = [];
  return {
    broadcast<T>(message: StateSyncMessage<T>): void {
      broadcasts.push(message as unknown as StateSyncMessage<unknown>);
    },
    onMessage<T>(callback: (message: StateSyncMessage<T>) => void): () => void {
      listeners.push(callback as unknown as (message: StateSyncMessage<unknown>) => void);
      return () => {
        const idx = listeners.indexOf(
          callback as unknown as (message: StateSyncMessage<unknown>) => void
        );
        if (idx > -1) listeners.splice(idx, 1);
      };
    },
    deliver(message: StateSyncMessage<unknown>): void {
      for (const listener of listeners) listener(message);
    },
    broadcasts,
  };
}

describe("$syncedState — Lamport clock", () => {
  test("rejects an incoming sync message whose clock equals the local clock", async () => {
    const sync = makeCapturedSyncAdapter();
    const sig = $syncedState<string>("lamport-equal", "init", { sync });
    // Wait for the loaded.then(...) microtask that registers the local effect.
    await Promise.resolve();

    // Drive a local write — entry.clock advances 0 → 1 and the effect
    // broadcasts (captured but never looped back).
    sig.value = "local";
    expect(sync.broadcasts.at(-1)?.clock).toBe(1);

    // A remote message with the same clock as the local clock must be
    // rejected: the rule is "strictly greater," not "greater or equal."
    sync.deliver({ key: "lamport-equal", value: "remote-equal", clock: 1 });

    expect(sig.value).toBe("local");
  });

  test("accepts an incoming sync message whose clock is strictly greater", async () => {
    const sync = makeCapturedSyncAdapter();
    const sig = $syncedState<string>("lamport-greater", "init", { sync });
    await Promise.resolve();

    sig.value = "local";

    sync.deliver({ key: "lamport-greater", value: "remote-greater", clock: 2 });

    expect(sig.value).toBe("remote-greater");
  });

  test("rejects an incoming sync message whose clock is strictly less", async () => {
    const sync = makeCapturedSyncAdapter();
    const sig = $syncedState<string>("lamport-less", "init", { sync });
    await Promise.resolve();

    sig.value = "local-1";
    sig.value = "local-2";

    sync.deliver({ key: "lamport-less", value: "stale", clock: 1 });

    expect(sig.value).toBe("local-2");
  });
});
