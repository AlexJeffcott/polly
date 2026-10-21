import type { Signal } from "@preact/signals-core";
import { Elysia } from "elysia";
import { createLamportClock } from "../core/clock";
import { findMatchingConfig } from "./route-match";
import type { PollyConfig, PollyResponseMetadata } from "./types";

/**
 * Broadcast message sent to connected clients
 */
interface BroadcastMessage {
  type: "effect";
  path: string;
  method: string;
  result: unknown;
  clock: { tick: number; contextId: string };
}

/**
 * Minimal WebSocket interface for broadcasting
 */
interface MinimalWebSocket {
  readyState: number;
  send(data: string): void;
}

/**
 * WebSocket broadcast manager
 */
class BroadcastManager {
  private connections = new Map<string, MinimalWebSocket>();

  register(clientId: string, ws: MinimalWebSocket) {
    this.connections.set(clientId, ws);
  }

  unregister(clientId: string) {
    this.connections.delete(clientId);
  }

  broadcast(message: BroadcastMessage, filter?: (clientId: string) => boolean) {
    const payload = JSON.stringify(message);

    for (const [clientId, ws] of this.connections.entries()) {
      if (filter && !filter(clientId)) continue;
      if (ws.readyState === 1) {
        // WebSocket.OPEN = 1
        ws.send(payload);
      }
    }
  }
}

/**
 * Main Polly Elysia plugin
 */
export function polly(config: PollyConfig = {}) {
  const isDev = process.env.NODE_ENV !== "production";
  const clock = createLamportClock("server");
  const broadcaster = new BroadcastManager();
  const clientStateByConnection = new Map<string, Record<string, Signal<unknown>>>();

  const app = new Elysia({ name: "polly" })
    // Add state to context
    .decorate("pollyState", {
      client: config.state?.client || {},
      server: config.state?.server || {},
    })
    .decorate("pollyClock", clock)
    .decorate("pollyBroadcast", broadcaster)

    // WebSocket endpoint for real-time updates
    .ws(config.websocketPath || "/polly/ws", {
      open(ws) {
        const clientId = ws.data.headers?.["x-client-id"] || crypto.randomUUID();
        broadcaster.register(clientId, ws.raw);

        // Send initial state sync
        ws.send(
          JSON.stringify({
            type: "state-sync",
            state: config.state?.client || {},
            clock: clock.now(),
          })
        );
      },
      close(ws) {
        const clientId = ws.data.headers?.["x-client-id"];
        if (clientId) {
          broadcaster.unregister(clientId);
          clientStateByConnection.delete(clientId);
        }
      },
      message(ws, message) {
        // Elysia parses a JSON text frame before calling this hook, so
        // `message` is usually already an object. `JSON.parse` on it threw,
        // no state-update was ever stored, and every `broadcastFilter` saw `{}`.
        const data = typeof message === "string" ? JSON.parse(message) : message;

        if (data.type === "state-update") {
          const clientId = ws.data.headers?.["x-client-id"];
          if (clientId) {
            clientStateByConnection.set(clientId, data.state);
          }
        }
      },
    })

    // Authorization hook (runs before handler)
    .onBeforeHandle(async ({ request, pollyState, body, params, status }) => {
      const method = request.method;
      const path = new URL(request.url).pathname;

      const authHandler = findMatchingConfig(config.authorization, method, path);

      if (authHandler) {
        const allowed = await authHandler({
          state: pollyState,
          body,
          params,
          headers: Object.fromEntries(request.headers.entries()),
        });

        // `status()` rather than a bare `new Response`: this hook is scoped
        // to the consumer, so Elysia folds its return type into every
        // consumer route's response map. A Response lands under 200 and
        // turns each route's Eden `data` into `T | Response`; `status(403)`
        // lands under 403, where Eden reports it as `error`.
        if (!allowed) {
          return status(403, "Unauthorized");
        }
      }
      return undefined;
    })

    // Response hook (runs after handler)
    .onAfterHandle(async ({ request, response, set, pollyClock, pollyBroadcast }) => {
      const method = request.method;
      const path = new URL(request.url).pathname;

      // Find matching effect config
      const effectConfig = findMatchingConfig(config.effects, method, path);

      // Tick clock
      pollyClock.tick();

      // If broadcast enabled, send to all connected clients
      // This works in both dev and prod for real-time updates
      if (effectConfig?.broadcast) {
        const broadcastMessage: BroadcastMessage = {
          type: "effect",
          path,
          method,
          result: response,
          clock: pollyClock.now(),
        };

        if (effectConfig.broadcastFilter) {
          pollyBroadcast.broadcast(broadcastMessage, (clientId) => {
            const clientState = clientStateByConnection.get(clientId) || {};
            return effectConfig.broadcastFilter?.(clientState) ?? false;
          });
        } else {
          pollyBroadcast.broadcast(broadcastMessage);
        }
      }

      // In production, skip expensive metadata operations
      if (!isDev) {
        return;
      }

      // DEV ONLY: Add Polly metadata to response for debugging/hot-reload
      const offlineConfig = findMatchingConfig(config.offline, method, path);
      const metadata: PollyResponseMetadata = {
        hasClientEffect: !!effectConfig,
        offline: offlineConfig,
        clock: pollyClock.now(),
      };

      // Attach the header through `set` and return nothing. Elysia merges
      // `set.headers` into whatever the handler produced — a plain value or
      // its own Response, status and headers intact. Returning a value here
      // would replace the handler's result, and because this hook is scoped
      // to the consumer, its return type would join every consumer route's
      // response type (a `Response` under 200, breaking Eden's `data`).
      set.headers["X-Polly-Metadata"] = JSON.stringify(metadata);
    })
    // Elysia scopes a plugin's lifecycle hooks to the plugin itself. Without
    // this, the authorization and metadata/broadcast hooks above ran only for
    // the plugin's own `/polly/ws` route and never for the consumer's routes.
    // `scoped` lifts them to the app that calls `.use(polly())`.
    .as("scoped");

  return app;
}
