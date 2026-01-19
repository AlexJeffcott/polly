// Sync adapter interface for cross-context state synchronization
// Abstracts the transport mechanism (chrome.runtime, BroadcastChannel, etc.)
//
// Architecture Decision: BroadcastChannel vs SharedWorker
// ------------------------------------------------------
// We currently use BroadcastChannel for web app sync because:
// - Simpler API with no lifecycle management complexity
// - Decentralized (aligns with local-first/offline-first architecture)
// - Better browser support (especially Safari and mobile)
// - Perfect for message-passing with Lamport clock conflict resolution
// - No single point of failure
//
// Future Consideration: SharedWorker Support
// ------------------------------------------
// SharedWorker could be added as an optional adapter for use cases requiring:
// - Central coordination point for complex multi-tab workflows
// - Shared WebSocket connections (one connection for all tabs)
// - Heavy computation done once and shared across tabs
// - Persistent background work when tabs are closed
// - Transaction coordination across tabs
//
// For most Polly use cases, BroadcastChannel's peer-to-peer model is preferred,
// but SharedWorker support could be valuable for advanced scenarios.

/**
 * Message format for state synchronization
 */
export interface StateSyncMessage<T = unknown> {
  key: string;
  value: T;
  clock: number;
}

/**
 * Sync adapter interface - abstracts the transport mechanism for state sync
 *
 * Different contexts use different transports:
 * - Chrome extensions: chrome.runtime messaging
 * - Web apps (multi-tab): BroadcastChannel
 * - PWAs: BroadcastChannel + Service Worker messaging
 * - Single-context: NoOp (no sync needed)
 */
export interface SyncAdapter {
  /**
   * Broadcast a state update to other contexts
   */
  broadcast<T>(message: StateSyncMessage<T>): void;

  /**
   * Register a callback for incoming state updates
   */
  onMessage<T>(callback: (message: StateSyncMessage<T>) => void): () => void;

  /**
   * Optional: Connect to the sync mechanism
   * Some transports require explicit connection setup
   */
  connect?(): Promise<void>;

  /**
   * Optional: Disconnect from the sync mechanism
   */
  disconnect?(): void;

  /**
   * Optional: Check if connected
   */
  isConnected?(): boolean;
}

/**
 * NoOp sync adapter for single-context scenarios (no sync needed)
 */
export class NoOpSyncAdapter implements SyncAdapter {
  broadcast<T>(_message: StateSyncMessage<T>): void {
    // No-op: single context, no need to sync
  }

  onMessage<T>(_callback: (message: StateSyncMessage<T>) => void): () => void {
    // No-op: no messages will ever arrive
    return () => {
      // Empty cleanup function - nothing to clean up for null adapter
    };
  }
}

/**
 * Chrome runtime sync adapter for Chrome extensions
 * Uses chrome.runtime.sendMessage for cross-context messaging
 */
export class ChromeRuntimeSyncAdapter implements SyncAdapter {
  private listeners: Array<(message: StateSyncMessage<unknown>) => void> = [];
  private port: chrome.runtime.Port | null = null;

  constructor() {
    // Set up listener for incoming messages
    if (typeof chrome !== "undefined" && chrome.runtime) {
      chrome.runtime.onMessage.addListener((message, _sender, _sendResponse) => {
        if (message.type === "STATE_SYNC") {
          this.listeners.forEach((listener) => {
            listener(message);
          });
        }
      });
    }
  }

  broadcast<T>(message: StateSyncMessage<T>): void {
    if (typeof chrome === "undefined" || !chrome.runtime) {
      console.warn("[SyncAdapter] chrome.runtime not available");
      return;
    }

    try {
      chrome.runtime.sendMessage({
        type: "STATE_SYNC",
        key: message.key,
        value: message.value,
        clock: message.clock,
      });
    } catch (error) {
      console.warn("[SyncAdapter] Failed to broadcast state update:", error);
    }
  }

  onMessage<T>(callback: (message: StateSyncMessage<T>) => void): () => void {
    this.listeners.push(callback as (message: StateSyncMessage<unknown>) => void);

    // Return cleanup function
    return () => {
      const index = this.listeners.indexOf(
        callback as (message: StateSyncMessage<unknown>) => void
      );
      if (index > -1) {
        this.listeners.splice(index, 1);
      }
    };
  }

  connect(): Promise<void> {
    // Chrome runtime is always connected
    return Promise.resolve();
  }

  disconnect(): void {
    this.listeners = [];
    if (this.port) {
      this.port.disconnect();
      this.port = null;
    }
  }

  isConnected(): boolean {
    return typeof chrome !== "undefined" && !!chrome.runtime;
  }
}

/**
 * BroadcastChannel sync adapter for web apps (multi-tab)
 * Uses BroadcastChannel API for cross-tab messaging
 */
export class BroadcastChannelSyncAdapter implements SyncAdapter {
  private channel: BroadcastChannel | null = null;
  private listeners: Array<(message: StateSyncMessage<unknown>) => void> = [];

  constructor(channelName = "polly-sync") {
    if (typeof BroadcastChannel !== "undefined") {
      this.channel = new BroadcastChannel(channelName);

      this.channel.onmessage = (event) => {
        if (event.data.type === "STATE_SYNC") {
          this.listeners.forEach((listener) => {
            listener(event.data);
          });
        }
      };
    } else {
      console.warn("[SyncAdapter] BroadcastChannel not available");
    }
  }

  broadcast<T>(message: StateSyncMessage<T>): void {
    if (!this.channel) {
      console.warn("[SyncAdapter] BroadcastChannel not initialized");
      return;
    }

    try {
      this.channel.postMessage({
        type: "STATE_SYNC",
        key: message.key,
        value: message.value,
        clock: message.clock,
      });
    } catch (error) {
      console.warn("[SyncAdapter] Failed to broadcast state update:", error);
    }
  }

  onMessage<T>(callback: (message: StateSyncMessage<T>) => void): () => void {
    this.listeners.push(callback as (message: StateSyncMessage<unknown>) => void);

    // Return cleanup function
    return () => {
      const index = this.listeners.indexOf(
        callback as (message: StateSyncMessage<unknown>) => void
      );
      if (index > -1) {
        this.listeners.splice(index, 1);
      }
    };
  }

  connect(): Promise<void> {
    // BroadcastChannel connects immediately on construction
    return Promise.resolve();
  }

  disconnect(): void {
    this.listeners = [];
    if (this.channel) {
      this.channel.close();
      this.channel = null;
    }
  }

  isConnected(): boolean {
    return this.channel !== null;
  }
}

/**
 * Detect available sync mechanisms and create appropriate adapter
 */
export function createSyncAdapter(): SyncAdapter {
  // Chrome extension context - use chrome.runtime
  if (typeof chrome !== "undefined" && chrome.runtime) {
    return new ChromeRuntimeSyncAdapter();
  }

  // Web app with multi-tab support - use BroadcastChannel
  if (typeof BroadcastChannel !== "undefined") {
    return new BroadcastChannelSyncAdapter();
  }

  // Single context or no sync available - use NoOp
  return new NoOpSyncAdapter();
}
