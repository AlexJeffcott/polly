// State primitives with optional sync and persistence

import { effect, type Signal, signal } from "@preact/signals";
import type { MessageBus } from "./message-bus";
import { createStorageAdapter, type StorageAdapter } from "./storage-adapter";
import { createSyncAdapter, type SyncAdapter } from "./sync-adapter";

/**
 * Signal extended with .loaded promise for hydration control
 */
type SignalWithLoaded<T> = Signal<T> & { loaded: Promise<void> };

/**
 * Signal extended with .loaded and .verify properties for verification tracking
 */
type SignalWithVerify<T> = Signal<T> & { loaded: Promise<void>; verify: T };

type StateEntry<T> = {
  signal: Signal<T>;
  clock: number; // Lamport clock for causal ordering
  loaded: Promise<void>;
  updating: boolean;
};

type StateOptions<T = unknown> = {
  // Legacy MessageBus support (deprecated, will be removed in v2.0)
  bus?: MessageBus;

  // New adapter system (recommended)
  storage?: StorageAdapter; // Custom storage adapter
  sync?: SyncAdapter; // Custom sync adapter

  // Behavior options
  debounceMs?: number; // Debounce storage writes
  validator?: (value: unknown) => value is T; // Runtime type validation
  verify?: boolean; // Enable verification tracking (creates plain object mirror)
};

const stateRegistry = new Map<string, StateEntry<unknown>>();

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
): Signal<T> & { loaded: Promise<void>; verify?: T } {
  const sig = createState(key, initialValue, {
    ...options,
    enableSync: true,
    enablePersist: true,
  });

  // Expose loaded promise for awaiting hydration
  const entry = stateRegistry.get(key);
  if (entry) {
    (sig as SignalWithLoaded<T>).loaded = entry.loaded;
  }

  return sig as Signal<T> & { loaded: Promise<void> };
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
    enableSync: true,
    enablePersist: false,
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
): Signal<T> & { loaded: Promise<void> } {
  const sig = createState(key, initialValue, {
    ...options,
    enableSync: false,
    enablePersist: true,
  });

  // Expose loaded promise for awaiting hydration
  const entry = stateRegistry.get(key);
  if (entry) {
    (sig as SignalWithLoaded<T>).loaded = entry.loaded;
  }

  return sig as Signal<T> & { loaded: Promise<void> };
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
  enableSync: boolean; // Whether to enable sync (avoid collision with sync?: SyncAdapter)
  enablePersist: boolean; // Whether to enable persistence
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

/**
 * Resolve storage and sync adapters with three-tier priority:
 * 1. Explicit adapters from options (highest priority)
 * 2. MessageBus adapters (legacy, deprecated)
 * 3. Auto-detected adapters (default behavior)
 */
function resolveAdapters(options: InternalStateOptions): {
  storage: StorageAdapter | null;
  sync: SyncAdapter | null;
} {
  // Priority 1: Explicit adapters (partial or full)
  if (options.storage || options.sync) {
    return {
      storage: options.storage || (options.enablePersist ? createStorageAdapter() : null),
      sync: options.sync || (options.enableSync ? createSyncAdapter() : null),
    };
  }

  // Priority 2: MessageBus (legacy support)
  // Note: MessageBus doesn't provide sync adapter, only Chrome storage
  if (options.bus) {
    return {
      storage: options.bus.adapters.storage,
      sync: options.enableSync ? createSyncAdapter() : null,
    };
  }

  // Priority 3: Auto-detect based on enableSync and enablePersist flags
  return {
    storage: options.enablePersist ? createStorageAdapter() : null,
    sync: options.enableSync ? createSyncAdapter() : null,
  };
}

function createState<T>(key: string, initialValue: T, options: InternalStateOptions<T>): Signal<T> {
  // Return existing signal if already registered
  if (stateRegistry.has(key)) {
    return stateRegistry.get(key)?.signal as Signal<T>;
  }

  const sig = signal(initialValue);

  // Create verification mirror if requested
  if (options.verify) {
    // Create plain object mirror for verification
    const mirror = JSON.parse(JSON.stringify(initialValue)) as T;
    (sig as SignalWithVerify<T>).verify = mirror;
  }

  const entry: StateEntry<T> = {
    signal: sig,
    clock: 0,
    loaded: Promise.resolve(),
    updating: false,
  };

  // Resolve adapters (explicit, MessageBus, or auto-detect)
  const adapters = resolveAdapters(options);

  // Load from storage if persist is enabled
  if (options.enablePersist && adapters.storage) {
    entry.loaded = loadFromStorage(key, sig, entry, adapters.storage, options.validator);
  }

  // Watch for changes after initial load
  entry.loaded.then(() => {
    let debounceTimer: NodeJS.Timeout | null = null;
    let previousValue = sig.value;
    let isFirstRun = true;

    // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Sync effect requires coordination of multiple state change scenarios
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

      // Update verification mirror if enabled
      if (options.verify) {
        const verifySignal = sig as SignalWithVerify<T>;
        if (verifySignal.verify) {
          Object.assign(verifySignal.verify, JSON.parse(JSON.stringify(value)));
        }
      }

      // Increment clock monotonically
      entry.clock++;

      const doUpdate = () => {
        // Persist to storage
        if (options.enablePersist && adapters.storage) {
          persistToStorage(key, value, entry.clock, adapters.storage);
        }

        // Broadcast to other contexts
        if (options.enableSync && adapters.sync) {
          broadcastUpdate(key, value, entry.clock, adapters.sync);
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
  if (options.enableSync && adapters.sync) {
    // Connect if needed (some adapters require explicit connection)
    if (adapters.sync.connect) {
      adapters.sync.connect();
    }

    // Register sync message listener
    adapters.sync.onMessage<T>((message) => {
      if (message.key !== key) return;

      const oldClock = entry.clock;

      // Lamport clock rule: Always update to max(local, received)
      // This maintains causal ordering even when rejecting updates
      entry.clock = Math.max(entry.clock, message.clock);

      // Only accept value updates if received clock is strictly greater than old local clock
      // This ensures we only apply causally newer updates
      if (message.clock > oldClock) {
        // Validate incoming value if validator provided
        if (options.validator && !options.validator(message.value)) {
          console.warn(
            `[Polly] State "${key}": Received invalid value from sync (clock: ${message.clock})`,
            message.value
          );
          return;
        }

        // Skip redundant updates (deep equality check)
        if (deepEqual(entry.signal.value, message.value)) {
          return;
        }

        applyUpdate(entry, message.value as T, message.clock);
      }
    });
  }

  stateRegistry.set(key, entry as StateEntry<unknown>);
  return sig;
}

async function loadFromStorage<T>(
  key: string,
  sig: Signal<T>,
  entry: StateEntry<T>,
  storage: StorageAdapter,
  validator?: (value: unknown) => value is T
): Promise<void> {
  try {
    const result = await storage.get([key, `${key}:clock`]);

    if (result[key] !== undefined) {
      const storedValue = result[key];

      // Validate stored value if validator provided
      if (validator) {
        if (validator(storedValue)) {
          sig.value = storedValue;
        } else {
          console.warn(
            `[Polly] State "${key}": Stored value failed validation, using initial value`,
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
    console.warn(`[Polly] Failed to load state from storage: ${key}`, error);
  }
}

function persistToStorage<T>(key: string, value: T, clock: number, storage: StorageAdapter): void {
  try {
    storage.set({
      [key]: value,
      [`${key}:clock`]: clock,
    });
  } catch (error) {
    console.warn(`[Polly] Failed to persist state to storage: ${key}`, error);
  }
}

function broadcastUpdate<T>(key: string, value: T, clock: number, sync: SyncAdapter): void {
  try {
    sync.broadcast({
      key,
      value,
      clock,
    });
  } catch (error) {
    console.warn(`[Polly] Failed to broadcast state update: ${key}`, error);
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
