// State primitives with optional sync and persistence

import { type Signal, effect, signal } from "@preact/signals";
import type { Context } from "../types/messages";
import { type MessageBus, getMessageBus } from "./message-bus";

type StateEntry<T> = {
  signal: Signal<T>;
  clock: number; // Lamport clock for causal ordering
  loaded: Promise<void>;
  updating: boolean;
};

type StateOptions<T = unknown> = {
  bus?: MessageBus; // Custom message bus (for testing)
  debounceMs?: number; // Debounce storage writes
  validator?: (value: unknown) => value is T; // Runtime type validation
};

const stateRegistry = new Map<string, StateEntry<unknown>>();

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Context detection requires multiple checks
function getCurrentContext(): Context {
  // Detect current context
  if (typeof chrome !== "undefined") {
    if (typeof chrome.devtools !== "undefined") {
      return "devtools";
    }
    if (typeof chrome.runtime !== "undefined") {
      try {
        if (typeof self !== "undefined" && "ServiceWorkerGlobalScope" in self) {
          return "background";
        }
        // biome-ignore lint/suspicious/noEmptyBlockStatements: ServiceWorkerGlobalScope check may fail in some contexts
      } catch {}
    }
  }

  if (typeof window !== "undefined" && typeof document !== "undefined") {
    if (typeof chrome === "undefined" || typeof chrome.runtime === "undefined") {
      return "page";
    }

    // Distinguish popup/options/offscreen from content scripts by URL
    if (
      typeof window.location !== "undefined" &&
      window.location.protocol === "chrome-extension:"
    ) {
      const path = window.location.pathname;
      if (path.includes("/popup")) return "popup";
      if (path.includes("/options")) return "options";
      if (path.includes("/offscreen")) return "offscreen";
      // Could also be a custom extension page, default to content
    }

    return "content";
  }

  return "background";
}

/**
 * Shared state: synced across all contexts AND persisted to storage
 *
 * Uses Lamport clock for conflict resolution. State is automatically:
 * - Loaded from chrome.storage on initialization
 * - Synced to other contexts via broadcast messages
 * - Persisted to chrome.storage on every change
 *
 * Available in: background, popup, options, devtools, content scripts
 * ⚠️ NOT available in page scripts (use content script state instead)
 *
 * @param key - Unique identifier for this state (e.g., "app-settings")
 * @param initialValue - Default value if nothing is in storage
 * @param options - Optional configuration (bus, debounceMs)
 * @returns Reactive signal that stays in sync across all contexts
 *
 * @example
 * ```typescript
 * // Define once, use everywhere
 * const settings = $sharedState("settings", { theme: "dark" })
 *
 * // Changes automatically sync
 * settings.value = { theme: "light" }
 * ```
 */
export function $sharedState<T>(
  key: string,
  initialValue: T,
  options: StateOptions<T> = {}
): Signal<T> {
  return createState(key, initialValue, {
    ...options,
    sync: true,
    persist: true,
  });
}

/**
 * Synced state: synced across all contexts but NOT persisted
 *
 * State is broadcast to all contexts in real-time but resets on extension reload.
 *
 * Available in: background, popup, options, devtools, content scripts
 * ⚠️ NOT available in page scripts
 *
 * @param key - Unique identifier for this state
 * @param initialValue - Default value
 * @param options - Optional configuration
 * @returns Reactive signal synced across contexts (but not persisted)
 *
 * @example
 * ```typescript
 * // Temporary shared state
 * const activeTabId = $syncedState("active-tab", null)
 * ```
 */
export function $syncedState<T>(
  key: string,
  initialValue: T,
  options: StateOptions<T> = {}
): Signal<T> {
  return createState(key, initialValue, {
    ...options,
    sync: true,
    persist: false,
  });
}

/**
 * Persisted state: persisted to storage but NOT synced across contexts
 *
 * Each context has its own copy of the state, persisted independently.
 *
 * Available in: background, popup, options, devtools, content scripts
 * ⚠️ NOT available in page scripts
 *
 * @param key - Unique identifier (use prefix like "popup:state" to avoid collisions)
 * @param initialValue - Default value
 * @param options - Optional configuration
 * @returns Reactive signal persisted to storage (but not synced)
 *
 * @example
 * ```typescript
 * // Each context has its own persisted state
 * const popupState = $persistedState("popup:last-panel", "home")
 * const devtoolsState = $persistedState("devtools:expanded", true)
 * ```
 */
export function $persistedState<T>(
  key: string,
  initialValue: T,
  options: StateOptions<T> = {}
): Signal<T> {
  return createState(key, initialValue, {
    ...options,
    sync: false,
    persist: true,
  });
}

/**
 * Local state: not synced, not persisted (like regular Preact signal)
 *
 * Simple reactive state that lives only in the current context.
 * Resets on reload or context restart.
 *
 * Available in: all contexts (including page scripts)
 *
 * @param initialValue - Default value
 * @returns Reactive signal (local only)
 *
 * @example
 * ```typescript
 * // Local UI state
 * const isLoading = $state(false)
 * const error = $state<string | null>(null)
 * ```
 */
export function $state<T>(initialValue: T): Signal<T> {
  return signal(initialValue);
}

type InternalStateOptions<T = unknown> = StateOptions<T> & {
  sync: boolean;
  persist: boolean;
};

// Deep equality check to prevent redundant updates
function deepEqual(a: unknown, b: unknown): boolean {
  if (a === b) return true;
  if (a == null || b == null) return false;
  if (typeof a !== "object" || typeof b !== "object") return false;

  const keysA = Object.keys(a);
  const keysB = Object.keys(b);

  if (keysA.length !== keysB.length) return false;

  for (const key of keysA) {
    if (!keysB.includes(key)) return false;
    if (!deepEqual((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]))
      return false;
  }

  return true;
}

function createState<T>(key: string, initialValue: T, options: InternalStateOptions<T>): Signal<T> {
  // Return existing signal if already registered
  if (stateRegistry.has(key)) {
    return stateRegistry.get(key)?.signal as Signal<T>;
  }

  const currentContext = getCurrentContext();

  // Page scripts should not have stateful operations
  // They are execution contexts for content scripts, not independent contexts
  if (currentContext === "page" && (options.sync || options.persist)) {
    const stateFn =
      options.sync && options.persist
        ? "$sharedState"
        : options.persist
          ? "$persistedState"
          : "$syncedState";

    throw new Error(
      `[web-ext] ${stateFn}() is not available in page context.\nPage scripts are execution contexts for content scripts and should not maintain state.\nUse state in the content script instead, or use $state() for local-only state.`
    );
  }

  const sig = signal(initialValue);

  const entry: StateEntry<T> = {
    signal: sig,
    clock: 0,
    loaded: Promise.resolve(),
    updating: false,
  };

  // Lazy bus initialization
  let bus: MessageBus | null = null;
  const getBus = () => {
    if (!bus && typeof chrome !== "undefined") {
      bus = options.bus || getMessageBus(currentContext);
    }
    return bus;
  };

  // Load from storage if persist is enabled
  if (options.persist) {
    entry.loaded = loadFromStorage(key, sig, entry, getBus(), options.validator);
  }

  // Watch for changes after initial load
  entry.loaded.then(() => {
    let debounceTimer: NodeJS.Timeout | null = null;
    let previousValue = sig.value;
    let isFirstRun = true;

    effect(() => {
      // Skip if update in progress (from incoming message)
      if (entry.updating) return;

      const value = sig.value;

      // Skip first run (effect fires immediately on registration)
      if (isFirstRun) {
        isFirstRun = false;
        return;
      }

      // Skip if value hasn't changed (deep equality check)
      if (deepEqual(value, previousValue)) {
        return;
      }

      previousValue = value;

      // Increment clock monotonically
      entry.clock++;

      const doUpdate = () => {
        // Persist to storage
        if (options.persist) {
          persistToStorage(key, value, entry.clock, getBus());
        }

        // Broadcast to other contexts
        if (options.sync) {
          broadcastUpdate(key, value, entry.clock, getBus());
        }
      };

      // Debounce if specified
      if (options.debounceMs) {
        if (debounceTimer) clearTimeout(debounceTimer);
        debounceTimer = setTimeout(doUpdate, options.debounceMs);
      } else {
        doUpdate();
      }
    });
  });

  // Listen for updates from other contexts (only if sync enabled)
  if (options.sync) {
    const messageBus = getBus();
    if (messageBus) {
      // Auto-connect for contexts that need it (popup, options, devtools)
      // Safe to call multiple times because:
      // - getMessageBus() returns a singleton per context
      // - connect() is idempotent (checks if port exists and returns early)
      // Background doesn't need to connect (it's the hub)
      // Content scripts connect explicitly when needed
      if (
        currentContext === "popup" ||
        currentContext === "options" ||
        currentContext === "devtools"
      ) {
        messageBus.connect(currentContext);
      }

      // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: State sync requires validation and conflict resolution
      messageBus.on("STATE_SYNC", async (payload) => {
        if (payload.key !== key) return undefined;

        const oldClock = entry.clock;

        // Lamport clock rule: Always update to max(local, received)
        // This maintains causal ordering even when rejecting updates
        entry.clock = Math.max(entry.clock, payload.clock);

        // Only accept value updates if received clock is strictly greater than old local clock
        // This ensures we only apply causally newer updates
        if (payload.clock > oldClock) {
          // Validate incoming value if validator provided
          if (options.validator && !options.validator(payload.value)) {
            console.warn(
              `[web-ext] State "${key}": Received invalid value from sync (clock: ${payload.clock})`,
              payload.value
            );
            return undefined;
          }

          // Skip redundant updates (deep equality check)
          if (deepEqual(entry.signal.value, payload.value)) {
            return undefined;
          }

          applyUpdate(entry, payload.value as T, payload.clock);
        }

        return undefined;
      });
    }
  }

  stateRegistry.set(key, entry as StateEntry<unknown>);
  return sig;
}

async function loadFromStorage<T>(
  key: string,
  sig: Signal<T>,
  entry: StateEntry<T>,
  bus: MessageBus | null,
  validator?: (value: unknown) => value is T
): Promise<void> {
  if (!bus) return;

  try {
    const result = await bus.adapters.storage.get([key, `${key}:clock`]);

    if (result[key] !== undefined) {
      const storedValue = result[key];

      // Validate stored value if validator provided
      if (validator) {
        if (validator(storedValue)) {
          sig.value = storedValue;
        } else {
          console.warn(
            `[web-ext] State "${key}": Stored value failed validation, using initial value`,
            storedValue
          );
        }
      } else {
        sig.value = storedValue as T;
      }
    }

    if (result[`${key}:clock`] !== undefined) {
      entry.clock = result[`${key}:clock`] as number;
    }
  } catch (error) {
    console.warn(`[web-ext] Failed to load state from storage: ${key}`, error);
  }
}

function persistToStorage<T>(key: string, value: T, clock: number, bus: MessageBus | null): void {
  if (!bus) return;

  try {
    bus.adapters.storage.set({
      [key]: value,
      [`${key}:clock`]: clock,
    });
  } catch (error) {
    console.warn(`Failed to persist state to storage: ${key}`, error);
  }
}

function broadcastUpdate<T>(key: string, value: T, clock: number, bus: MessageBus | null): void {
  if (!bus) return;

  try {
    bus.broadcast({
      type: "STATE_SYNC",
      key,
      value,
      clock,
    });
  } catch (error) {
    console.warn(`Failed to broadcast state update: ${key}`, error);
  }
}

function applyUpdate<T>(entry: StateEntry<T>, value: T, clock: number): void {
  entry.updating = true;
  entry.signal.value = value;
  entry.clock = clock;
  entry.updating = false;
}

/**
 * Get state by key (useful for retrieving state without re-creating)
 */
export function getStateByKey<T>(key: string): Signal<T> | undefined {
  const entry = stateRegistry.get(key);
  return entry?.signal as Signal<T> | undefined;
}

/**
 * Clear state registry (useful for testing)
 */
export function clearStateRegistry(): void {
  stateRegistry.clear();
}
