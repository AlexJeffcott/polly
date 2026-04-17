/**
 * peer-repo-server — Phase 1 server-side factory for the Polly peer-relay
 * transport. Constructs an Automerge-Repo `Repo` wired to a WebSocket server
 * and a NodeFS storage backend, ready to relay sync messages between
 * connected $peerState clients.
 *
 * The "always-on peer" role for $peerState lives here. The server holds a
 * full Automerge replica of every document, participates in the sync protocol
 * as an ordinary peer, and persists state to disk so the next process restart
 * picks up where the previous one left off. Server-side cron, HTTP handlers,
 * and other compute can open document handles on the returned Repo and mutate
 * them; mutations propagate to connected clients through the same sync
 * protocol that handles client-to-client traffic.
 *
 * The plan originally called this an "Elysia plugin," but Automerge's
 * `WebSocketServerAdapter` requires an `isomorphic-ws` `WebSocketServer`
 * instance — not Elysia's native WebSocket — so the cleanest first cut is a
 * standalone factory that runs its own `ws` server. Elysia integration for
 * authenticated upgrades is a Phase 1.1 follow-up that wraps this factory.
 *
 * @example
 * ```ts
 * import { createPeerRepoServer } from "@fairfox/polly";
 *
 * const server = await createPeerRepoServer({
 *   port: 3030,
 *   storagePath: "./data/polly-peer",
 * });
 *
 * // Open a document handle on the server's Repo for cron or compute work.
 * const handle = server.repo.create({ counter: 0 });
 *
 * // On shutdown:
 * await server.close();
 * ```
 */

// Heavy peer-relay dependencies (@automerge/automerge-repo, ws) are dynamic
// imports loaded only when createPeerRepoServer is actually called. Static
// imports at this file's top level were hoisted into @fairfox/polly/elysia's
// module-init chain, breaking Elysia apps that don't use peer state and
// don't install the automerge peer deps. Types come from the static package
// references — TypeScript only reads them for shape, so no runtime cost is
// incurred.
import type { Repo as RepoType } from "@automerge/automerge-repo/slim";
import type { WebSocketServerAdapter as WebSocketServerAdapterType } from "@automerge/automerge-repo-network-websocket";
import type { NodeFSStorageAdapter as NodeFSStorageAdapterType } from "@automerge/automerge-repo-storage-nodefs";
import type * as wsType from "ws";

// `@types/ws` uses CJS `export = WebSocket` with WebSocketServer hanging off
// the namespace. Under the project's bundler module resolution, the namespace
// import gives us access to both the constructor and the type.
type WebSocketServer = wsType.WebSocketServer;

export interface CreatePeerRepoServerOptions {
  /** Port to listen on. The factory creates its own `WebSocketServer` and
   * binds to this port. */
  port: number;
  /** Filesystem directory for the NodeFS storage adapter. The directory is
   * created on demand. Defaults to `./automerge-repo-data` (Automerge's own
   * default). */
  storagePath?: string;
  /** Hostname interface to bind to. Defaults to all interfaces. */
  host?: string;
  /** Override the `WebSocketServer` instance entirely. When provided, `port`
   * and `host` are ignored and the caller is responsible for the lifecycle.
   * Useful for tests that want to bind to a random port. */
  webSocketServer?: WebSocketServer;
}

export interface PeerRepoServer {
  /** A configured Repo participating as the always-on peer. Server-side
   * cron and HTTP handlers can open document handles on this directly. */
  repo: RepoType;
  /** The underlying WebSocket server. Exposed for advanced use such as
   * health checks or graceful shutdown coordination. */
  webSocketServer: WebSocketServer;
  /** The Automerge network adapter wrapping the WebSocket server. */
  adapter: WebSocketServerAdapterType;
  /** The NodeFS storage adapter writing to {@link CreatePeerRepoServerOptions.storagePath}. */
  storage: NodeFSStorageAdapterType;
  /** Tear down the server: disconnect peers, flush storage, close the
   * underlying WebSocket server. Returns a promise that resolves once the
   * tear-down is complete. */
  close: () => Promise<void>;
}

/**
 * Construct a Polly peer-relay server. Returns a Repo that participates as
 * the always-on peer, the underlying WebSocket server and storage adapter
 * for advanced use, and a close function for orderly shutdown.
 *
 * Applications typically call this once at startup, hold the returned
 * `repo` reference for cron and compute work, and wire the close function
 * into their process shutdown signal handlers.
 */
export async function createPeerRepoServer(
  options: CreatePeerRepoServerOptions
): Promise<PeerRepoServer> {
  // Dynamic imports keep automerge-repo and ws out of the static module
  // graph. Apps that never call this function — which is most of them —
  // never pay the dependency cost and don't need the peer packages
  // installed at all.
  const [{ Repo }, { WebSocketServerAdapter }, { NodeFSStorageAdapter }, ws] = await Promise.all([
    import("@automerge/automerge-repo/slim"),
    import("@automerge/automerge-repo-network-websocket"),
    import("@automerge/automerge-repo-storage-nodefs"),
    import("ws"),
  ]);

  // Construct the WebSocket server first and wait until it is actually
  // listening before wiring up the Repo. Using the constructor callback
  // avoids the race where the 'listening' event fires before our listener
  // is attached (the callback form is reliable across Node and Bun).
  const wss = await (options.webSocketServer
    ? Promise.resolve(options.webSocketServer)
    : new Promise<WebSocketServer>((resolve, reject) => {
        const created: WebSocketServer = new ws.WebSocketServer(
          {
            port: options.port,
            ...(options.host !== undefined && { host: options.host }),
          },
          () => resolve(created)
        );
        created.once("error", reject);
      }));

  // The cast bridges a @types/ws identity quirk: Automerge's adapter type
  // expects WebSocketServer with options.WebSocket typed via isomorphic-ws's
  // CJS-style namespace, and our direct `ws` import resolves through a
  // different path with the same runtime shape but a structurally distinct
  // TypeScript type. The runtime is identical, the cast names that fact.
  const adapter = new WebSocketServerAdapter(
    wss as unknown as ConstructorParameters<typeof WebSocketServerAdapter>[0]
  );
  const storage = new NodeFSStorageAdapter(options.storagePath);

  const repo = new Repo({
    network: [adapter],
    storage,
  });

  // Force the storage subsystem to finish initialising before returning. The
  // Repo constructor is synchronous, but its NetworkSubsystem holds back the
  // peer-metadata JOIN until storageSubsystem.id() resolves. If a client
  // connects before that resolution lands, the handshake stalls indefinitely.
  // Awaiting storageId() drains the relevant microtask chain and guarantees
  // the server is ready to accept peers when this factory returns.
  await repo.storageId();

  return {
    repo,
    webSocketServer: wss,
    adapter,
    storage,
    close: async () => {
      // Forcibly terminate any still-open client sockets before closing the
      // server, otherwise wss.close() can hang waiting for orderly drain when
      // a peer disappeared without a clean disconnect. We then fire the
      // server close without awaiting its callback — the underlying socket
      // is released immediately by terminate(), and waiting for the close
      // callback can hang under Bun even after every client is gone.
      for (const client of wss.clients) {
        try {
          client.terminate();
        } catch {
          // best effort
        }
      }
      try {
        await repo.shutdown();
      } catch {
        // best effort — automerge-repo's xstate DocHandle machine can
        // throw "Cycle detected" during teardown when sync messages are
        // still in flight.
      }
      try {
        wss.close();
      } catch {
        // best effort
      }
    },
  };
}
