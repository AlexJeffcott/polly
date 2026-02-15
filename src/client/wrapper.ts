// @ts-nocheck - Optional peer dependencies (elysia, @elysiajs/eden)
import { treaty } from "@elysiajs/eden";
import { type Signal, signal } from "@preact/signals-core";
import { createLamportClock } from "../core/clock";
import type { PollyResponseMetadata } from "../elysia/types";
import { deserializeFunction } from "../utils/function-serialization";

/**
 * Offline queue entry
 */
interface QueuedRequest {
  id: string;
  method: string;
  path: string;
  body: unknown;
  optimisticResult?: unknown;
  timestamp: number;
}

/**
 * Client-side state management
 */
interface ClientState {
  isOnline: Signal<boolean>;
  isSyncing: Signal<boolean>;
  queuedRequests: Signal<QueuedRequest[]>;
}

/**
 * Polly client options
 */
export interface PollyClientOptions {
  /**
   * Client state signals that should be synced
   */
  state?: Record<string, Signal<unknown>>;

  /**
   * Callback when online/offline status changes
   */
  onOfflineChange?: (isOnline: boolean) => void;

  /**
   * Enable WebSocket for real-time updates (default: true in dev, false in prod)
   */
  websocket?: boolean;

  /**
   * WebSocket path (default: '/polly/ws')
   */
  websocketPath?: string;
}

/**
 * Create a Polly-enhanced Eden client
 *
 * In DEV mode:
 * - Processes server metadata for hot reloading
 * - Executes client effects from server
 * - Handles offline queueing
 * - Connects WebSocket for real-time updates
 *
 * In PROD mode:
 * - Minimal wrapper (client effects are bundled)
 * - Optional WebSocket for real-time features
 * - Offline queueing still works
 *
 * Example:
 * ```typescript
 * import { createPollyClient } from '@fairfox/polly/client';
 * import { $syncedState } from '@fairfox/polly';
 * import type { app } from './server';
 *
 * const clientState = {
 *   todos: $syncedState('todos', []),
 *   user: $syncedState('user', null),
 * };
 *
 * export const api = createPollyClient<typeof app>('http://localhost:3000', {
 *   state: clientState,
 *   websocket: true,
 * });
 * ```
 */
export function createPollyClient<T extends Record<string, unknown>>(
  url: string,
  options: PollyClientOptions = {}
) {
  const isDev = process.env.NODE_ENV !== "production";
  const baseClient = treaty<T>(url);
  const clock = createLamportClock("client");

  // Client state
  const clientState: ClientState = {
    isOnline: signal(typeof navigator !== "undefined" ? navigator.onLine : true),
    isSyncing: signal(false),
    queuedRequests: signal<QueuedRequest[]>([]),
  };

  // WebSocket connection for real-time updates (opt-in in prod)
  let ws: WebSocket | null = null;
  const shouldUseWebSocket = options.websocket !== undefined ? options.websocket : isDev;

  if (shouldUseWebSocket && typeof WebSocket !== "undefined") {
    const wsPath = options.websocketPath || "/polly/ws";
    const wsUrl = url.replace(/^http/, "ws") + wsPath;

    try {
      ws = new WebSocket(wsUrl);

      ws.addEventListener("open", () => {
        console.log("[Polly] WebSocket connected");
      });

      ws.addEventListener("message", (event) => {
        const message = JSON.parse(event.data);

        if (message.type === "state-sync") {
          // Initial state sync
          Object.assign(options.state || {}, message.state);
        } else if (message.type === "effect") {
          // Remote effect triggered by another client (broadcast)
          console.log("[Polly] Received broadcast effect:", message);
          // In production, handle this via your bundled effects
          // In dev, the effect handler comes from metadata
        }
      });

      ws.addEventListener("error", (error) => {
        // biome-ignore lint/suspicious/noConsole: Error logging is intentional
        console.error("[Polly] WebSocket error:", error);
      });
    } catch (error) {
      // biome-ignore lint/suspicious/noConsole: Error logging is intentional
      console.error("[Polly] Failed to create WebSocket:", error);
    }
  }

  // Online/offline listeners (browser only)
  if (typeof window !== "undefined") {
    window.addEventListener("online", () => {
      clientState.isOnline.value = true;
      options.onOfflineChange?.(true);
      processQueue();
    });

    window.addEventListener("offline", () => {
      clientState.isOnline.value = false;
      options.onOfflineChange?.(false);
    });
  }

  /**
   * Process queued requests when back online
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Queue processing requires complex branching logic
  async function processQueue() {
    if (clientState.queuedRequests.value.length === 0) return;

    clientState.isSyncing.value = true;

    const queue = [...clientState.queuedRequests.value];
    clientState.queuedRequests.value = [];

    for (const req of queue) {
      try {
        // Replay request
        const response = await fetch(url + req.path, {
          method: req.method,
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(req.body),
        });

        const result = await response.json();

        // In dev mode, process metadata
        if (isDev) {
          const metadataHeader = response.headers.get("X-Polly-Metadata");
          if (metadataHeader) {
            const metadata: PollyResponseMetadata = JSON.parse(metadataHeader);

            // Handle merge if optimistic update was used
            if (req.optimisticResult && metadata.offline?.merge) {
              const mergeStrategy = metadata.offline.merge;

              if (mergeStrategy === "replace") {
                // Replace optimistic with server result (default)
                // The client effect will handle this
              } else if (typeof mergeStrategy === "function") {
                // TODO: Update local state with merged result
                // const merged = mergeStrategy(req.optimisticResult, result);
                // Apply merged state to local signals
              }
            }

            // Execute client effect
            if (metadata.clientEffect) {
              const handler = deserializeFunction(metadata.clientEffect.handler);
              handler({
                result,
                body: req.body,
                state: { client: options.state || {}, server: {} },
                params: {},
                clock: metadata.clock,
              });
            }
          }
        }
      } catch (error) {
        // biome-ignore lint/suspicious/noConsole: Error logging is intentional
        console.error("[Polly] Failed to replay request:", req, error);
        // Re-queue on failure
        clientState.queuedRequests.value.push(req);
      }
    }

    clientState.isSyncing.value = false;
  }

  // Return the base client with additional Polly features
  return {
    ...baseClient,
    $polly: {
      state: clientState,
      clock,
      ws,
      /**
       * Manually process queued requests
       */
      sync: processQueue,
    },
  };
}
