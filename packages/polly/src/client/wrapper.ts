// @ts-nocheck - Optional peer dependencies (elysia, @elysiajs/eden)
import { treaty } from "@elysiajs/eden";
import { type Signal, signal } from "@preact/signals-core";
import { createLamportClock, type LamportClock } from "../core/clock";
import { extractRouteParams, findMatchingConfig, findMatchingEntry } from "../elysia/route-match";
import type {
  ClientEffectConfig,
  OfflineConfig,
  PollyResponseMetadata,
  RoutePattern,
} from "../elysia/types";

/** Eden treaty leaf methods that execute a request. */
const HTTP_METHODS = new Set(["get", "post", "put", "patch", "delete", "head", "options"]);

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
   * Client-side effect handlers, keyed by the same route pattern used in the
   * server config (e.g. `'POST /todos'`). The wrapper looks up handlers here
   * after a successful request — handlers are imported, never shipped from
   * the server.
   */
  clientEffects?: Record<RoutePattern, ClientEffectConfig["client"]>;

  /**
   * Offline behaviour keyed by route pattern, mirroring the server `offline`
   * config. When a request is made while offline and its route has
   * `queue: true`, the wrapper queues it (applying any `optimistic` update) and
   * replays it on reconnect instead of letting the network call throw. Like
   * {@link clientEffects}, this is imported locally — never shipped from the
   * server — because an offline client cannot fetch the server's metadata.
   */
  offline?: Record<RoutePattern, OfflineConfig>;

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
 * Apply a server `state-sync` payload to the client state map. The map holds
 * SIGNALS (`{ value }`); the server sends plain values, so each value is
 * assigned INTO its signal. `Object.assign`-ing the container instead would
 * replace the signal objects with plain values and break every reactive
 * `state.x.value` read — the next render then throws "Cannot read properties of
 * null (reading 'value')".
 */
function applyStateSync(state: PollyClientOptions["state"], incoming: unknown): void {
  if (!state || !incoming || typeof incoming !== "object") return;
  const target = state as Record<string, { value: unknown }>;
  for (const [key, value] of Object.entries(incoming as Record<string, unknown>)) {
    const sig = target[key];
    if (sig && typeof sig === "object" && "value" in sig) {
      sig.value = value;
    }
  }
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
    isOnline: signal(typeof navigator === "undefined" ? true : navigator.onLine),
    isSyncing: signal(false),
    queuedRequests: signal<QueuedRequest[]>([]),
  };

  // WebSocket connection for real-time updates (opt-in in prod)
  let ws: WebSocket | null = null;
  const shouldUseWebSocket = options.websocket === undefined ? isDev : options.websocket;

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
          applyStateSync(options.state, message.state);
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
   * Run the locally-registered client effect for a route, if one matches.
   * Handlers live in `options.clientEffects` keyed by route pattern — they are
   * imported, never deserialised from the wire. Path params (`:id`) are
   * extracted from the concrete path so handlers like `DELETE /todos/:id` get
   * `params.id`.
   */
  function runClientEffect(
    method: string,
    path: string,
    body: unknown,
    result: unknown,
    eventClock: LamportClock
  ): void {
    const entry = findMatchingEntry(options.clientEffects, method, path);
    if (!entry?.config) return;
    entry.config({
      result,
      body,
      state: { client: options.state || {}, server: {} },
      params: extractRouteParams(entry.pattern, path),
      clock: eventClock,
    });
  }

  /**
   * Process queued requests when back online
   */
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

        // Process metadata and run the client effect with the real server
        // result, replacing the optimistic update applied while offline.
        const metadataHeader = response.headers.get("X-Polly-Metadata");
        const metadata: PollyResponseMetadata | undefined = metadataHeader
          ? JSON.parse(metadataHeader)
          : undefined;
        if (metadata?.clock) clock.update(metadata.clock);
        runClientEffect(req.method, req.path, req.body, result, metadata?.clock ?? clock.now());
      } catch (error) {
        // biome-ignore lint/suspicious/noConsole: Error logging is intentional
        console.error("[Polly] Failed to replay request:", req, error);
        // Re-queue on failure
        clientState.queuedRequests.value.push(req);
      }
    }

    clientState.isSyncing.value = false;
  }

  let queueSeq = 0;

  /**
   * Queue a write that was attempted while offline, so it replays on reconnect
   * instead of throwing. Returns an Eden-shaped result so callers that `await`
   * the request (and read `.data`) don't blow up offline.
   */
  function enqueue(method: string, path: string, body: unknown, offlineConfig: OfflineConfig) {
    const optimisticResult = offlineConfig.optimistic?.(body);
    queueSeq += 1;
    const req: QueuedRequest = {
      id: `${clock.now().contextId}-${queueSeq}`,
      method,
      path,
      body,
      optimisticResult,
      timestamp: Date.now(),
    };
    clientState.queuedRequests.value = [...clientState.queuedRequests.value, req];
    // The optimistic result (if any) is held on the queue entry; the real
    // client effect runs on drain with the server result. Surfacing it
    // optimistically in the UI before drain needs the per-route `merge` story
    // (still unimplemented), so we don't apply it here to avoid a duplicate.
    return { data: optimisticResult ?? null, error: null, response: undefined, status: 0 };
  }

  /**
   * A request reached the server (online). Read the metadata header and run the
   * matching client effect locally with the real result.
   */
  function applyOnlineResult(method: string, path: string, body: unknown, edenResult: unknown) {
    const result = edenResult as { data?: unknown; response?: Response } | undefined;
    const response = result?.response;
    const header = response?.headers?.get?.("X-Polly-Metadata");
    const metadata: PollyResponseMetadata | undefined = header ? JSON.parse(header) : undefined;
    if (metadata?.clock) clock.update(metadata.clock);
    runClientEffect(method, path, body, result?.data, metadata?.clock ?? clock.now());
  }

  /**
   * Invoke a leaf request method (e.g. `api.todos.post(body)`). Offline writes
   * with a queued offline config are queued; everything else delegates to Eden
   * and then runs the local client effect.
   */
  async function invoke(segments: string[], method: string, args: unknown[]): Promise<unknown> {
    const httpMethod = method.toUpperCase();
    const path = `/${segments.join("/")}`;
    const body = args[0];

    // The isOnline signal is a cached view updated by the window 'offline'
    // event, which can lag the actual transition; navigator.onLine is the
    // authoritative live state at call time. Treat either saying "offline" as
    // offline so a write made the instant connectivity drops still queues.
    const isOffline =
      !clientState.isOnline.value ||
      (typeof navigator !== "undefined" && navigator.onLine === false);
    if (isOffline) {
      const offlineConfig = findMatchingConfig(options.offline, httpMethod, path);
      if (offlineConfig?.queue) return enqueue(httpMethod, path, body, offlineConfig);
    }

    // Delegate to the real Eden client by walking the same property chain the
    // caller used (api.todos[id].patch → baseClient.todos[id].patch).
    let node: Record<string, unknown> = baseClient as Record<string, unknown>;
    for (const seg of segments) node = node[seg] as Record<string, unknown>;
    const edenMethod = node[method] as (...a: unknown[]) => Promise<unknown>;
    const edenResult = await edenMethod(...args);
    applyOnlineResult(httpMethod, path, body, edenResult);
    return edenResult;
  }

  const pollyApi = {
    state: clientState,
    clock,
    ws,
    /** Manually process queued requests. */
    sync: processQueue,
  };

  // Eden's `treaty` returns a PROXY that builds request paths lazily via
  // property access (api.auth.login.post → POST /auth/login; api.todos[id].delete
  // → DELETE /todos/:id). To run client effects and offline queueing we mirror
  // that path-building with our own proxy, intercepting only the leaf HTTP
  // method call. Spreading or naively wrapping Eden ({ ...baseClient }) discards
  // its lazy proxy and leaves every route undefined.
  function makePathProxy(segments: string[]): unknown {
    // Target is a function so the proxy stays callable where Eden allows it.
    const target = () => undefined;
    return new Proxy(target, {
      get(_t, prop) {
        if (prop === "$polly") return pollyApi;
        // Don't masquerade as a thenable when an intermediate node is awaited.
        if (prop === "then" || typeof prop === "symbol") return undefined;
        if (HTTP_METHODS.has(prop)) {
          return (...args: unknown[]) => invoke(segments, prop, args);
        }
        return makePathProxy([...segments, prop]);
      },
    });
  }

  return makePathProxy([]) as typeof baseClient & { $polly: typeof pollyApi };
}
