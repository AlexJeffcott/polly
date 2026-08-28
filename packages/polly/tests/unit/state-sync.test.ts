import { afterEach, describe, expect, test } from "bun:test";
import { $syncedState, clearStateRegistry } from "@/shared/lib/state";
import type { StateSyncMessage, SyncAdapter } from "@/shared/lib/sync-adapter";

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

/** Let the `entry.loaded.then(...)` microtask register the local effect. */
function flushMicrotasks(): Promise<void> {
  return Promise.resolve();
}

describe("$syncedState — sync stays two-way", () => {
  test("keeps broadcasting local changes after receiving one", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("sync-both-ways", "initial", { sync });
    await flushMicrotasks();

    sync.deliver({ key: "sync-both-ways", value: "remote", clock: 1 });
    expect(sig.value).toBe("remote");

    sig.value = "local-after-remote";

    const broadcast = sync.broadcasts.find((m) => m.value === "local-after-remote");
    expect(broadcast?.key).toBe("sync-both-ways");
  });

  test("does not echo an incoming update back to the other contexts", async () => {
    const sync = makeFakeSyncAdapter();
    $syncedState<string>("sync-no-echo", "initial", { sync });
    await flushMicrotasks();

    sync.deliver({ key: "sync-no-echo", value: "remote", clock: 1 });

    expect(sync.broadcasts).toEqual([]);
  });

  test("broadcasts a local write that reverts to the pre-incoming value", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("sync-revert", "initial", { sync });
    await flushMicrotasks();

    sync.deliver({ key: "sync-revert", value: "remote", clock: 1 });
    sig.value = "initial";

    const broadcast = sync.broadcasts.find((m) => m.value === "initial");
    expect(broadcast?.key).toBe("sync-revert");
  });

  test("still broadcasts after a second incoming update", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("sync-two-incoming", "initial", { sync });
    await flushMicrotasks();

    sync.deliver({ key: "sync-two-incoming", value: "remote-1", clock: 1 });
    sync.deliver({ key: "sync-two-incoming", value: "remote-2", clock: 2 });
    sig.value = "local";

    expect(sync.broadcasts.map((m) => m.value)).toEqual(["local"]);
  });

  test("an incoming update leaves no debounce timer that later broadcasts it", async () => {
    const sync = makeFakeSyncAdapter();
    $syncedState<string>("sync-debounce-no-echo", "initial", { sync, debounceMs: 5 });
    await flushMicrotasks();

    sync.deliver({ key: "sync-debounce-no-echo", value: "remote", clock: 1 });
    await new Promise((resolve) => setTimeout(resolve, 25));

    expect(sync.broadcasts).toEqual([]);
  });

  test("broadcasts a debounced local change made after an incoming update", async () => {
    const sync = makeFakeSyncAdapter();
    const sig = $syncedState<string>("sync-debounce-after", "initial", { sync, debounceMs: 5 });
    await flushMicrotasks();

    sync.deliver({ key: "sync-debounce-after", value: "remote", clock: 1 });
    sig.value = "local-after-remote";
    await new Promise((resolve) => setTimeout(resolve, 25));

    expect(sync.broadcasts.map((m) => m.value)).toEqual(["local-after-remote"]);
  });
});
