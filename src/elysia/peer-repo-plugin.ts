// @ts-nocheck - Optional peer dependencies (elysia, @automerge/automerge-repo*)
/**
 * peerRepo — Elysia plugin that runs a Polly peer-relay server alongside an
 * Elysia application and exposes the server's Repo on the Elysia context.
 *
 * The Phase 1 plan originally framed the relay server as an Elysia plugin
 * that registers a WebSocket route on Elysia's native socket layer. That
 * design does not work directly: Automerge's WebSocketServerAdapter requires
 * an `isomorphic-ws` WebSocketServer instance, and Elysia's WebSocket layer
 * is built on Bun's native WebSocket API, which is a different shape. The
 * realistic Phase 1 cut is therefore a *lifecycle* plugin: it runs
 * createPeerRepoServer on its own port during Elysia startup, decorates the
 * Elysia context so route handlers can reach the resulting Repo, and tears
 * the server down during Elysia shutdown. Authenticated WebSocket upgrades
 * via Elysia's hook system are a Phase 1.1 follow-up that requires either
 * a custom Bun-native NetworkAdapter or an upgrade-time auth bridge.
 *
 * @example
 * ```ts
 * import { Elysia } from "elysia";
 * import { peerRepo } from "@fairfox/polly/elysia";
 *
 * const app = new Elysia()
 *   .use(peerRepo({ port: 3030, storagePath: "./data/polly-peer" }))
 *   .get("/stats", ({ pollyPeerRepo }) => {
 *     return { peers: pollyPeerRepo.peers.length };
 *   })
 *   .listen(8080);
 * ```
 */

import { Elysia } from "elysia";
import {
  type CreatePeerRepoServerOptions,
  createPeerRepoServer,
  type PeerRepoServer,
} from "../shared/lib/peer-repo-server";

export interface PeerRepoPluginOptions extends CreatePeerRepoServerOptions {
  /** Optional path for a health endpoint that returns peer count and storage
   * id. Set to false to skip the health route entirely. Defaults to
   * "/polly/peer/health". */
  healthPath?: string | false;
}

/**
 * Elysia plugin that boots a Polly peer-relay server alongside the host app
 * and decorates the context with `pollyPeerRepo` (the Repo) and
 * `pollyPeerServer` (the full {@link PeerRepoServer} for advanced use).
 *
 * The plugin starts the relay server during Elysia's onStart lifecycle and
 * shuts it down during onStop, so route handlers and cron jobs can use the
 * decorated Repo throughout the request lifetime without managing the
 * underlying transport themselves.
 */
export function peerRepo(options: PeerRepoPluginOptions) {
  // The plugin holds a single PeerRepoServer for the lifetime of the Elysia
  // app. It is created during onStart so the listening socket is bound and
  // ready before any request handler can reach it.
  let server: PeerRepoServer | undefined;

  const healthPath =
    options.healthPath === false ? null : (options.healthPath ?? "/polly/peer/health");

  let app = new Elysia({ name: "polly-peer-repo" })
    .decorate("pollyPeerRepo", null as unknown as PeerRepoServer["repo"] | null)
    .decorate("pollyPeerServer", null as unknown as PeerRepoServer | null)
    .onStart(async () => {
      server = await createPeerRepoServer(options);
      // Decorate after construction so handlers see the live Repo. Elysia's
      // decorate is mutable in-place when called on the running instance.
      app.decorate("pollyPeerRepo", server.repo);
      app.decorate("pollyPeerServer", server);
    })
    .onStop(async () => {
      if (server) {
        await server.close();
        server = undefined;
      }
    });

  if (healthPath) {
    app = app.get(healthPath, () => {
      if (!server) {
        return { status: "starting", peers: 0 };
      }
      return {
        status: "running",
        peers: server.repo.peers.length,
        port: options.port,
      };
    });
  }

  return app;
}
