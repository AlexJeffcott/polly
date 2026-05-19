// @ts-nocheck - Optional peer dependencies (elysia, @elysiajs/eden)
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
      // @ts-expect-error - Elysia WebSocket types from optional peer dependency
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
      // @ts-expect-error - Elysia WebSocket types from optional peer dependency
      close(ws) {
        const clientId = ws.data.headers?.["x-client-id"];
        if (clientId) {
          broadcaster.unregister(clientId);
          clientStateByConnection.delete(clientId);
        }
      },
      // @ts-expect-error - Elysia WebSocket types from optional peer dependency
      message(ws, message) {
        // Handle client state updates
        const data = JSON.parse(message as unknown as string);

        if (data.type === "state-update") {
          const clientId = ws.data.headers?.["x-client-id"];
          if (clientId) {
            clientStateByConnection.set(clientId, data.state);
          }
        }
      },
    })

    // Authorization hook (runs before handler)
    // @ts-expect-error - Elysia context types from optional peer dependency
    .onBeforeHandle(async ({ request, pollyState, body, params }) => {
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

        if (!allowed) {
          return new Response("Unauthorized", { status: 403 });
        }
      }
    })

    // Response hook (runs after handler)
    // @ts-expect-error - Elysia context types from optional peer dependency
    .onAfterHandle(
      async ({ request, response, _pollyState, pollyClock, pollyBroadcast, _body, _params }) => {
        const method = request.method;
        const path = new URL(request.url).pathname;

        // Find matching effect config
        const effectConfig = findMatchingConfig(config.effects, method, path);

        // Tick clock
        pollyClock.tick();

        // If broadcast enabled, send to all connected clients
        // This works in both dev and prod for real-time updates
        if (effectConfig?.broadcast) {
          const broadcastMessage = {
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
          return response;
        }

        // DEV ONLY: Add Polly metadata to response for debugging/hot-reload
        const offlineConfig = findMatchingConfig(config.offline, method, path);
        const metadata: PollyResponseMetadata = {
          hasClientEffect: !!effectConfig,
          offline: offlineConfig,
          clock: pollyClock.now(),
        };

        // Attach metadata as header
        return new Response(JSON.stringify(response), {
          headers: {
            "Content-Type": "application/json",
            "X-Polly-Metadata": JSON.stringify(metadata),
          },
        });
      }
    );

  return app;
}
