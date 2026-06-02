/**
 * Tests for adapter-factory.ts — the storage+sync adapter composition layer.
 *
 * The underlying backends are already covered (storage-adapter,
 * sync-adapter); this suite pins the factory wiring: custom-adapter
 * passthrough, the single-tab override, the detection fall-through, and the
 * per-context constructors. In the bun test environment auto-detection lands
 * on MemoryStorageAdapter (no chrome / no indexedDB) and
 * BroadcastChannelSyncAdapter (bun has a real BroadcastChannel), which the
 * instanceof assertions rely on.
 *
 * Each created sync adapter is disconnected in afterEach so no
 * BroadcastChannel is left open.
 */

import { afterEach, describe, expect, test } from "bun:test";
import {
  createChromeAdapters,
  createMockAdapters,
  createNodeAdapters,
  createStateAdapters,
  createWebAdapters,
  type StateAdapters,
} from "@/shared/lib/adapter-factory";
import {
  ChromeStorageAdapter,
  IndexedDBAdapter,
  MemoryStorageAdapter,
} from "@/shared/lib/storage-adapter";
import {
  BroadcastChannelSyncAdapter,
  ChromeRuntimeSyncAdapter,
  NoOpSyncAdapter,
  type SyncAdapter,
} from "@/shared/lib/sync-adapter";

// Disconnect every adapter set a test produces so BroadcastChannels close.
const created: StateAdapters[] = [];
function record(adapters: StateAdapters): StateAdapters {
  created.push(adapters);
  return adapters;
}

afterEach(() => {
  for (const { sync } of created.splice(0)) {
    sync.disconnect?.();
  }
});

/** A storage stub distinct from every real adapter class, for identity checks. */
function stubStorage() {
  return {
    get: async () => ({}),
    set: async () => {},
    remove: async () => {},
  };
}

/** A sync stub distinct from every real adapter class. */
function stubSync(): SyncAdapter {
  return {
    broadcast: () => {},
    onMessage: () => () => {},
  };
}

// ---------------------------------------------------------------------------
// createStateAdapters
// ---------------------------------------------------------------------------

describe("createStateAdapters", () => {
  test("auto-detects both adapters when no options are given", () => {
    const { storage, sync } = record(createStateAdapters());
    expect(storage).toBeInstanceOf(MemoryStorageAdapter);
    expect(sync).toBeInstanceOf(BroadcastChannelSyncAdapter);
  });

  test("passes through both custom adapters unchanged", () => {
    const storage = stubStorage();
    const sync = stubSync();
    const result = createStateAdapters({ storage, sync });
    expect(result.storage).toBe(storage);
    expect(result.sync).toBe(sync);
  });

  test("with only a custom storage, the sync adapter is still auto-detected", () => {
    const storage = stubStorage();
    const result = record(createStateAdapters({ storage }));
    // The custom storage is used verbatim...
    expect(result.storage).toBe(storage);
    // ...and a real sync adapter is created rather than left undefined (the
    // `storage && sync` guard must not early-return on storage alone).
    expect(result.sync).toBeInstanceOf(BroadcastChannelSyncAdapter);
  });

  test("with only a custom sync, the storage adapter is still auto-detected", () => {
    const sync = stubSync();
    const result = createStateAdapters({ sync });
    expect(result.sync).toBe(sync);
    expect(result.storage).toBeInstanceOf(MemoryStorageAdapter);
  });

  test("singleTab forces a NoOp sync (storage still auto-detected)", () => {
    const { storage, sync } = createStateAdapters({ singleTab: true });
    expect(storage).toBeInstanceOf(MemoryStorageAdapter);
    expect(sync).toBeInstanceOf(NoOpSyncAdapter);
  });

  test("a custom sync wins over singleTab", () => {
    const sync = stubSync();
    const result = createStateAdapters({ sync, singleTab: true });
    expect(result.sync).toBe(sync);
  });
});

// ---------------------------------------------------------------------------
// Per-context factories
// ---------------------------------------------------------------------------

describe("createChromeAdapters", () => {
  test("builds Chrome storage + Chrome runtime sync", () => {
    const { storage, sync } = record(createChromeAdapters());
    expect(storage).toBeInstanceOf(ChromeStorageAdapter);
    expect(sync).toBeInstanceOf(ChromeRuntimeSyncAdapter);
  });
});

describe("createWebAdapters", () => {
  test("defaults to IndexedDB storage + BroadcastChannel sync", () => {
    const { storage, sync } = record(createWebAdapters());
    expect(storage).toBeInstanceOf(IndexedDBAdapter);
    expect(sync).toBeInstanceOf(BroadcastChannelSyncAdapter);
  });

  test("singleTab swaps the sync adapter for NoOp", () => {
    const { storage, sync } = record(createWebAdapters({ singleTab: true }));
    expect(storage).toBeInstanceOf(IndexedDBAdapter);
    expect(sync).toBeInstanceOf(NoOpSyncAdapter);
  });

  test("threads channelName into the BroadcastChannel", () => {
    const { sync } = record(createWebAdapters({ channelName: "custom-channel" }));
    expect((sync as unknown as { channel: BroadcastChannel }).channel.name).toBe("custom-channel");
  });

  test("defaults the BroadcastChannel name when none is given", () => {
    const { sync } = record(createWebAdapters());
    expect((sync as unknown as { channel: BroadcastChannel }).channel.name).toBe("polly-sync");
  });

  test("threads dbName into the IndexedDB adapter", () => {
    const { storage } = record(createWebAdapters({ dbName: "custom-db" }));
    expect((storage as unknown as { dbName: string }).dbName).toBe("custom-db");
  });
});

describe("createNodeAdapters", () => {
  test("builds in-memory storage + NoOp sync", () => {
    const { storage, sync } = record(createNodeAdapters());
    expect(storage).toBeInstanceOf(MemoryStorageAdapter);
    expect(sync).toBeInstanceOf(NoOpSyncAdapter);
  });
});

describe("createMockAdapters", () => {
  test("builds in-memory storage + NoOp sync", () => {
    const { storage, sync } = record(createMockAdapters());
    expect(storage).toBeInstanceOf(MemoryStorageAdapter);
    expect(sync).toBeInstanceOf(NoOpSyncAdapter);
  });
});
