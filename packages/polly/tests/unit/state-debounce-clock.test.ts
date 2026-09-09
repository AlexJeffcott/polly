import { afterEach, describe, expect, test } from "bun:test";
import { $sharedState, $syncedState, clearStateRegistry } from "@/shared/lib/state";
import type { StorageAdapter } from "@/shared/lib/storage-adapter";
import type { StateSyncMessage, SyncAdapter } from "@/shared/lib/sync-adapter";

/**
 * polly#167: a pending debounce timer must not adopt somebody else's clock.
 *
 * `doUpdate` closed over the local `value` but read `entry.clock` when the
 * timer fired. The incoming-message handler raises `entry.clock` to any
 * message's clock — including one whose value it rejects — so the deferred
 * write paired this context's value with another write's clock, persisted the
 * pair, and broadcast it.
 *
 * Both halves are durable. `loadFromStorage` restores the clock, so the
 * context comes back holding the wrong value while claiming the higher clock,
 * and every later message carrying the right value at that clock is refused by
 * the strictly-greater rule. The broadcast half is worse than inert: a third
 * context still below that clock accepts the stale value and then refuses the
 * real one.
 */

afterEach(() => {
  clearStateRegistry();
});

interface FakeSyncAdapter extends SyncAdapter {
  /** Deliver a message as though it arrived from another context. */
  deliver: (message: StateSyncMessage<unknown>) => void;
  /** Everything the local effect broadcast. Never looped back. */
  broadcasts: Array<StateSyncMessage<unknown>>;
}

function makeFakeSyncAdapter(): FakeSyncAdapter {
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

interface FakeStorageAdapter extends StorageAdapter {
  /** Everything written, in write order. */
  writes: Array<Record<string, unknown>>;
  /** The current contents, as a reload would read them. */
  contents: Record<string, unknown>;
}

function makeFakeStorageAdapter(seed: Record<string, unknown> = {}): FakeStorageAdapter {
  const contents: Record<string, unknown> = { ...seed };
  const writes: Array<Record<string, unknown>> = [];
  return {
    async get<T = unknown>(keys: string[]): Promise<Record<string, T>> {
      const out: Record<string, unknown> = {};
      for (const k of keys) {
        if (k in contents) out[k] = contents[k];
      }
      return out as Record<string, T>;
    },
    async set(items: Record<string, unknown>): Promise<void> {
      writes.push({ ...items });
      Object.assign(contents, items);
    },
    async remove(keys: string[]): Promise<void> {
      for (const k of keys) delete contents[k];
    },
    writes,
    contents,
  };
}

/** Let the `entry.loaded.then(...)` microtask register the local effect. */
function flushMicrotasks(): Promise<void> {
  return Promise.resolve();
}

/**
 * A `$sharedState` hydrates from storage before its effect exists, and a write
 * made before then is adopted as the baseline rather than broadcast. Await the
 * load, then the microtask that registers the effect.
 */
async function ready(sig: { loaded: Promise<void> }): Promise<void> {
  await sig.loaded;
  await flushMicrotasks();
}

/** Let a `debounceMs` window elapse, and the async storage write settle. */
function advancePast(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms + 20));
}

const DEBOUNCE_MS = 30;

describe("a debounced write against an incoming update — the storage half", () => {
  test("storage holds the incoming pair, not the superseded local one", async () => {
    const sync = makeFakeSyncAdapter();
    const storage = makeFakeStorageAdapter();
    const sig = $sharedState<string>("d-storage", "initial", {
      sync,
      storage,
      debounceMs: DEBOUNCE_MS,
    });
    await ready(sig);

    sig.value = "V_local";
    sync.deliver({ key: "d-storage", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    expect(sig.value).toBe("V_remote");
    expect(storage.contents["d-storage"]).toBe("V_remote");
    expect(storage.contents["d-storage:clock"]).toBe(5);
  });

  test("no write ever pairs a value with another write's clock", async () => {
    const sync = makeFakeSyncAdapter();
    const storage = makeFakeStorageAdapter();
    const sig = $sharedState<string>("d-pairs", "initial", {
      sync,
      storage,
      debounceMs: DEBOUNCE_MS,
    });
    await ready(sig);

    sig.value = "V_local";
    sync.deliver({ key: "d-pairs", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    // The local write happened at clock 1. Clock 5 belongs to V_remote alone.
    for (const write of storage.writes) {
      if (write["d-pairs"] === "V_local") {
        expect(write["d-pairs:clock"]).toBe(1);
      }
      if (write["d-pairs:clock"] === 5) {
        expect(write["d-pairs"]).toBe("V_remote");
      }
    }
  });

  test("in-memory and stored state agree after an incoming update", async () => {
    const sync = makeFakeSyncAdapter();
    const storage = makeFakeStorageAdapter();
    const sig = $sharedState<string>("d-agree", "initial", { sync, storage });
    await ready(sig);

    sync.deliver({ key: "d-agree", value: "V_remote", clock: 3 });
    await advancePast(0);

    expect(storage.contents["d-agree"]).toBe(sig.value);
    expect(storage.contents["d-agree:clock"]).toBe(3);
  });

  test("the restored pair is one a peer can correct", async () => {
    // The durable half: a context reloading from the stale pair claimed clock
    // 5 while holding V_local, and refused every later V_remote @ 5.
    const sync = makeFakeSyncAdapter();
    const storage = makeFakeStorageAdapter();
    const first = $sharedState<string>("d-reload", "initial", {
      sync,
      storage,
      debounceMs: DEBOUNCE_MS,
    });
    await ready(first);

    first.value = "V_local";
    sync.deliver({ key: "d-reload", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    clearStateRegistry();

    const reloadSync = makeFakeSyncAdapter();
    const second = $sharedState<string>("d-reload", "initial", {
      sync: reloadSync,
      storage,
    });
    await second.loaded;
    await flushMicrotasks();

    expect(second.value).toBe("V_remote");
  });
});

describe("a debounced write against an incoming update — the broadcast half", () => {
  test("the superseded local value is not broadcast", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("d-nobroadcast", "initial", {
      sync,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    sig.value = "V_local";
    sync.deliver({ key: "d-nobroadcast", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    expect(sync.broadcasts.map((m) => m.value)).not.toContain("V_local");
  });

  test("no broadcast pairs a value with a clock from a different write", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("d-broadcast-pairs", "initial", {
      sync,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    sig.value = "V_local";
    sync.deliver({ key: "d-broadcast-pairs", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    for (const m of sync.broadcasts) {
      expect(m.clock).not.toBe(5);
    }
  });

  test("a third context below the remote clock cannot be given the stale value", async () => {
    // The three-context case. A and B share a channel; C joins it, still at
    // clock 0. A's superseded write, broadcast at clock 5, would be accepted
    // by C and would then make C refuse the real V_remote @ 5.
    const channel = makeFakeSyncAdapter();
    const a = $syncedState<string>("d-three", "initial", {
      sync: channel,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    a.value = "V_local";
    channel.deliver({ key: "d-three", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    // Replay onto a fresh context exactly what A put on the wire.
    const sentByA = channel.broadcasts.filter((m) => m.key === "d-three");
    clearStateRegistry();

    const cSync = makeFakeSyncAdapter();
    const c = $syncedState<string>("d-three", "initial", { sync: cSync });
    await flushMicrotasks();

    for (const m of sentByA) cSync.deliver(m);
    cSync.deliver({ key: "d-three", value: "V_remote", clock: 5 });

    expect(c.value).toBe("V_remote");
  });
});

describe("a message the handler rejects still raises the clock", () => {
  test("a pending write does not adopt the clock of a value that was refused", async () => {
    // The Lamport rule runs on EVERY message: `entry.clock = max(local,
    // received)` happens before the strictly-greater test, so a message whose
    // value is never applied still moves the clock the pending timer read.
    const sync = makeFakeSyncAdapter();
    const storage = makeFakeStorageAdapter();
    const sig = $sharedState<string>("d-rejected", "initial", {
      sync,
      storage,
      debounceMs: DEBOUNCE_MS,
      validator: (v): v is string => v !== "REFUSED",
    });
    await ready(sig);

    sig.value = "V_local";
    sync.deliver({ key: "d-rejected", value: "REFUSED", clock: 9 });
    await advancePast(DEBOUNCE_MS);

    // The value the validator refused is not held, and the local write went
    // out at its own clock of 1 — not at 9.
    expect(sig.value).toBe("V_local");
    expect(storage.contents["d-rejected"]).toBe("V_local");
    expect(storage.contents["d-rejected:clock"]).toBe(1);
    expect(sync.broadcasts.find((m) => m.value === "V_local")?.clock).toBe(1);
  });
});

describe("the edges the fix must not break", () => {
  test("a second local write inside the window broadcasts above the remote clock", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("d-second-write", "initial", {
      sync,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    sig.value = "V_local";
    sync.deliver({ key: "d-second-write", value: "V_remote", clock: 5 });
    sig.value = "V_local_2";
    await advancePast(DEBOUNCE_MS);

    const sent = sync.broadcasts.find((m) => m.value === "V_local_2");
    expect(sent).toBeDefined();
    expect(sent?.clock).toBeGreaterThan(5);
    expect(sig.value).toBe("V_local_2");
  });

  test("an incoming value equal to the pending one leaves the timer armed", async () => {
    // `applyUpdate` is never reached — the deep-equality skip returns first —
    // so nothing cancels this timer and the local write must still go out.
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("d-equal", "initial", {
      sync,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    sig.value = "SAME";
    sync.deliver({ key: "d-equal", value: "SAME", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    expect(sync.broadcasts.map((m) => m.value)).toContain("SAME");
    expect(sig.value).toBe("SAME");
  });

  test("debounceMs without persistence has the broadcast half only", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("d-nopersist", "initial", {
      sync,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    sig.value = "V_local";
    sync.deliver({ key: "d-nopersist", value: "V_remote", clock: 5 });
    await advancePast(DEBOUNCE_MS);

    expect(sig.value).toBe("V_remote");
    expect(sync.broadcasts.map((m) => m.value)).not.toContain("V_local");
  });

  test("an undisturbed debounced write still persists and broadcasts", async () => {
    const sync = makeFakeSyncAdapter();
    const storage = makeFakeStorageAdapter();
    const sig = $sharedState<string>("d-plain", "initial", {
      sync,
      storage,
      debounceMs: DEBOUNCE_MS,
    });
    await ready(sig);

    sig.value = "V_local";
    await advancePast(DEBOUNCE_MS);

    expect(storage.contents["d-plain"]).toBe("V_local");
    expect(storage.contents["d-plain:clock"]).toBe(1);
    expect(sync.broadcasts.find((m) => m.value === "V_local")?.clock).toBe(1);
  });

  test("rapid local writes still coalesce into one", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("d-coalesce", "initial", {
      sync,
      debounceMs: DEBOUNCE_MS,
    });
    await flushMicrotasks();

    sig.value = "a";
    sig.value = "b";
    sig.value = "c";
    await advancePast(DEBOUNCE_MS);

    expect(sync.broadcasts).toHaveLength(1);
    expect(sync.broadcasts[0]?.value).toBe("c");
  });
});
