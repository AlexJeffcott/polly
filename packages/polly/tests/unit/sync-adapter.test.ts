/**
 * Tests for sync-adapter — the cross-context state sync backends.
 *
 * NoOpSyncAdapter (single context), BroadcastChannelSyncAdapter (multi-tab
 * web, exercised against bun's real BroadcastChannel), ChromeRuntimeSyncAdapter
 * (extension contexts, driven against a faked `chrome` global), and the
 * createSyncAdapter context-detection factory.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import {
  BroadcastChannelSyncAdapter,
  ChromeRuntimeSyncAdapter,
  createSyncAdapter,
  NoOpSyncAdapter,
  type StateSyncMessage,
} from "@/shared/lib/sync-adapter";

const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 15));

const msg = <T>(over: Partial<StateSyncMessage<T>> = {}): StateSyncMessage<T> =>
  ({ key: "k", value: "v" as unknown as T, clock: 1, ...over }) as StateSyncMessage<T>;

// console.warn is captured per test so the warn paths can be asserted and
// the output does not pollute the test log.
let warnings: unknown[][] = [];
let originalWarn: typeof console.warn;
beforeEach(() => {
  warnings = [];
  originalWarn = console.warn;
  console.warn = (...args: unknown[]) => {
    warnings.push(args);
  };
});
afterEach(() => {
  console.warn = originalWarn;
});

describe("NoOpSyncAdapter", () => {
  test("broadcast is a no-op that does not throw", () => {
    const a = new NoOpSyncAdapter();
    expect(() => a.broadcast(msg())).not.toThrow();
  });

  test("onMessage never fires and returns a callable cleanup", () => {
    const a = new NoOpSyncAdapter();
    let fired = false;
    const cleanup = a.onMessage(() => {
      fired = true;
    });
    expect(typeof cleanup).toBe("function");
    expect(() => cleanup()).not.toThrow();
    expect(fired).toBe(false);
  });
});

describe("BroadcastChannelSyncAdapter", () => {
  let channelName: string;
  let adapters: BroadcastChannelSyncAdapter[];
  beforeEach(() => {
    // A unique channel per test keeps broadcasts from leaking across tests.
    channelName = `polly-test-${warnings.length}-${Math.floor(performance.now())}`;
    adapters = [];
  });
  afterEach(() => {
    for (const a of adapters) a.disconnect();
  });
  const make = (): BroadcastChannelSyncAdapter => {
    const a = new BroadcastChannelSyncAdapter(channelName);
    adapters.push(a);
    return a;
  };

  test("reports connected after construction and resolves connect()", async () => {
    const a = make();
    expect(a.isConnected()).toBe(true);
    await expect(a.connect()).resolves.toBeUndefined();
  });

  test("delivers a broadcast STATE_SYNC message to another adapter on the same channel", async () => {
    const sender = make();
    const receiver = make();
    const received: StateSyncMessage[] = [];
    receiver.onMessage((m) => received.push(m));
    sender.broadcast(msg({ key: "doc", value: 42, clock: 9 }));
    await flush();
    expect(received).toHaveLength(1);
    expect(received[0]?.key).toBe("doc");
    expect(received[0]?.value).toBe(42);
    expect(received[0]?.clock).toBe(9);
  });

  test("the onMessage cleanup unsubscribes the listener", async () => {
    const sender = make();
    const receiver = make();
    const received: StateSyncMessage[] = [];
    const cleanup = receiver.onMessage((m) => received.push(m));
    cleanup();
    sender.broadcast(msg());
    await flush();
    expect(received).toHaveLength(0);
  });

  test("disconnect closes the channel and reports not connected", () => {
    const a = make();
    a.disconnect();
    expect(a.isConnected()).toBe(false);
  });

  test("broadcast after disconnect warns instead of throwing", () => {
    const a = make();
    a.disconnect();
    expect(() => a.broadcast(msg())).not.toThrow();
    expect(warnings.some((w) => String(w[0]).includes("not initialized"))).toBe(true);
  });

  test("ignores channel messages that are not STATE_SYNC", async () => {
    const receiver = make();
    const received: StateSyncMessage[] = [];
    receiver.onMessage((m) => received.push(m));
    // Post a foreign message straight onto the underlying channel.
    const raw = new BroadcastChannel(channelName);
    raw.postMessage({ type: "SOMETHING_ELSE", key: "x" });
    await flush();
    raw.close();
    expect(received).toHaveLength(0);
  });
});

interface FakeChrome {
  chrome: {
    runtime: {
      onMessage: { addListener: (cb: (m: unknown, s: unknown, r: unknown) => void) => void };
      sendMessage: (m: unknown) => void;
    };
  };
  fire: (m: unknown) => void;
  sent: unknown[];
  throwOnSend: () => void;
}

function installFakeChrome(): FakeChrome {
  let listener: ((m: unknown, s: unknown, r: unknown) => void) | undefined;
  const sent: unknown[] = [];
  let shouldThrow = false;
  const fake: FakeChrome = {
    chrome: {
      runtime: {
        onMessage: {
          addListener: (cb) => {
            listener = cb;
          },
        },
        sendMessage: (m) => {
          if (shouldThrow) throw new Error("sendMessage blew up");
          sent.push(m);
        },
      },
    },
    fire: (m) => listener?.(m, {}, () => {}),
    sent,
    throwOnSend: () => {
      shouldThrow = true;
    },
  };
  (globalThis as unknown as { chrome: unknown }).chrome = fake.chrome;
  return fake;
}

describe("ChromeRuntimeSyncAdapter", () => {
  let hadChrome: boolean;
  let savedChrome: unknown;
  beforeEach(() => {
    hadChrome = "chrome" in globalThis;
    savedChrome = (globalThis as unknown as { chrome?: unknown }).chrome;
  });
  afterEach(() => {
    if (hadChrome) {
      (globalThis as unknown as { chrome: unknown }).chrome = savedChrome;
    } else {
      delete (globalThis as unknown as { chrome?: unknown }).chrome;
    }
  });

  test("broadcasts a STATE_SYNC payload through chrome.runtime.sendMessage", () => {
    const fake = installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    a.broadcast(msg({ key: "doc", value: 7, clock: 3 }));
    expect(fake.sent).toEqual([{ type: "STATE_SYNC", key: "doc", value: 7, clock: 3 }]);
  });

  test("dispatches an incoming STATE_SYNC message to its listeners", () => {
    const fake = installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    const received: StateSyncMessage[] = [];
    a.onMessage((m) => received.push(m));
    fake.fire({ type: "STATE_SYNC", key: "doc", value: 5, clock: 2 });
    expect(received).toHaveLength(1);
    expect(received[0]?.key).toBe("doc");
  });

  test("ignores incoming messages that are not STATE_SYNC", () => {
    const fake = installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    const received: StateSyncMessage[] = [];
    a.onMessage((m) => received.push(m));
    fake.fire({ type: "OTHER", key: "doc" });
    expect(received).toHaveLength(0);
  });

  test("onMessage cleanup removes the listener", () => {
    const fake = installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    const received: StateSyncMessage[] = [];
    const cleanup = a.onMessage((m) => received.push(m));
    cleanup();
    fake.fire({ type: "STATE_SYNC", key: "doc", value: 1, clock: 1 });
    expect(received).toHaveLength(0);
  });

  test("isConnected reflects chrome availability", () => {
    installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    expect(a.isConnected()).toBe(true);
    delete (globalThis as unknown as { chrome?: unknown }).chrome;
    expect(a.isConnected()).toBe(false);
  });

  test("connect resolves and disconnect clears listeners", async () => {
    const fake = installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    await expect(a.connect()).resolves.toBeUndefined();
    const received: StateSyncMessage[] = [];
    a.onMessage((m) => received.push(m));
    a.disconnect();
    fake.fire({ type: "STATE_SYNC", key: "doc", value: 1, clock: 1 });
    expect(received).toHaveLength(0);
  });

  test("a throwing sendMessage is swallowed with a warning", () => {
    const fake = installFakeChrome();
    const a = new ChromeRuntimeSyncAdapter();
    fake.throwOnSend();
    expect(() => a.broadcast(msg())).not.toThrow();
    expect(warnings.some((w) => String(w[0]).includes("Failed to broadcast"))).toBe(true);
  });

  test("broadcast warns when chrome.runtime is unavailable", () => {
    delete (globalThis as unknown as { chrome?: unknown }).chrome;
    const a = new ChromeRuntimeSyncAdapter();
    a.broadcast(msg());
    expect(warnings.some((w) => String(w[0]).includes("chrome.runtime not available"))).toBe(true);
  });
});

describe("createSyncAdapter context detection", () => {
  let hadChrome: boolean;
  let savedChrome: unknown;
  let hadBC: boolean;
  let savedBC: unknown;
  beforeEach(() => {
    hadChrome = "chrome" in globalThis;
    savedChrome = (globalThis as unknown as { chrome?: unknown }).chrome;
    hadBC = "BroadcastChannel" in globalThis;
    savedBC = (globalThis as unknown as { BroadcastChannel?: unknown }).BroadcastChannel;
  });
  afterEach(() => {
    if (hadChrome) (globalThis as unknown as { chrome: unknown }).chrome = savedChrome;
    else delete (globalThis as unknown as { chrome?: unknown }).chrome;
    if (hadBC) (globalThis as unknown as { BroadcastChannel: unknown }).BroadcastChannel = savedBC;
    else delete (globalThis as unknown as { BroadcastChannel?: unknown }).BroadcastChannel;
  });

  test("prefers ChromeRuntimeSyncAdapter when chrome.runtime is present", () => {
    installFakeChrome();
    expect(createSyncAdapter()).toBeInstanceOf(ChromeRuntimeSyncAdapter);
  });

  test("uses BroadcastChannelSyncAdapter in a web context with no chrome", () => {
    delete (globalThis as unknown as { chrome?: unknown }).chrome;
    const adapter = createSyncAdapter();
    expect(adapter).toBeInstanceOf(BroadcastChannelSyncAdapter);
    (adapter as BroadcastChannelSyncAdapter).disconnect();
  });

  test("falls back to NoOpSyncAdapter when neither chrome nor BroadcastChannel exists", () => {
    delete (globalThis as unknown as { chrome?: unknown }).chrome;
    delete (globalThis as unknown as { BroadcastChannel?: unknown }).BroadcastChannel;
    expect(createSyncAdapter()).toBeInstanceOf(NoOpSyncAdapter);
  });
});

describe("sync-adapter listener-cleanup and construction edge branches", () => {
  test("ChromeRuntime: removing a listener twice does not disturb the others", () => {
    const fake = installFakeChrome();
    const hadChrome = "chrome" in globalThis;
    try {
      const a = new ChromeRuntimeSyncAdapter();
      const first: number[] = [];
      const second: number[] = [];
      const cleanupFirst = a.onMessage(() => first.push(1));
      a.onMessage(() => second.push(1));
      cleanupFirst();
      // A second cleanup finds index -1; the guard must skip the splice so
      // the still-registered second listener is not collaterally removed.
      cleanupFirst();
      fake.fire({ type: "STATE_SYNC", key: "k", value: "v", clock: 1 });
      expect(second).toHaveLength(1);
    } finally {
      if (!hadChrome) delete (globalThis as unknown as { chrome?: unknown }).chrome;
    }
  });

  test("BroadcastChannel: removing a listener twice does not disturb the others", async () => {
    const name = `polly-cleanup-${Math.floor(performance.now())}`;
    const sender = new BroadcastChannelSyncAdapter(name);
    const receiver = new BroadcastChannelSyncAdapter(name);
    try {
      const first: number[] = [];
      const second: number[] = [];
      const cleanupFirst = receiver.onMessage(() => first.push(1));
      receiver.onMessage(() => second.push(1));
      cleanupFirst();
      cleanupFirst();
      sender.broadcast(msg());
      await flush();
      expect(second).toHaveLength(1);
    } finally {
      sender.disconnect();
      receiver.disconnect();
    }
  });

  test("BroadcastChannel: the default channel name is polly-sync", async () => {
    // One adapter on the default name must reach one constructed explicitly
    // on "polly-sync" — proving the default literal, not just any default.
    const def = new BroadcastChannelSyncAdapter();
    const explicit = new BroadcastChannelSyncAdapter("polly-sync");
    try {
      const received: StateSyncMessage[] = [];
      explicit.onMessage((m) => received.push(m));
      def.broadcast(msg({ key: "default-name" }));
      await flush();
      expect(received.some((m) => m.key === "default-name")).toBe(true);
    } finally {
      def.disconnect();
      explicit.disconnect();
    }
  });

  test("BroadcastChannel: warns and stays disconnected when the API is unavailable", () => {
    const saved = (globalThis as unknown as { BroadcastChannel?: unknown }).BroadcastChannel;
    delete (globalThis as unknown as { BroadcastChannel?: unknown }).BroadcastChannel;
    try {
      const a = new BroadcastChannelSyncAdapter();
      expect(warnings.some((w) => String(w[0]).includes("BroadcastChannel not available"))).toBe(
        true
      );
      expect(a.isConnected()).toBe(false);
      // broadcast on an uninitialised channel warns rather than throwing.
      expect(() => a.broadcast(msg())).not.toThrow();
    } finally {
      (globalThis as unknown as { BroadcastChannel: unknown }).BroadcastChannel = saved;
    }
  });

  test("BroadcastChannel: a throwing postMessage is swallowed with a warning", () => {
    const a = new BroadcastChannelSyncAdapter(`polly-throw-${Math.floor(performance.now())}`);
    try {
      // Swap in a channel whose postMessage throws to drive the catch.
      (a as unknown as { channel: { postMessage: () => void; close: () => void } }).channel = {
        postMessage: () => {
          throw new Error("postMessage blew up");
        },
        close: () => {},
      };
      expect(() => a.broadcast(msg())).not.toThrow();
      expect(warnings.some((w) => String(w[0]).includes("Failed to broadcast"))).toBe(true);
    } finally {
      a.disconnect();
    }
  });
});
