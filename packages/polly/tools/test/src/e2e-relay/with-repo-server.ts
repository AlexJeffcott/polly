/**
 * @fairfox/polly/test/e2e-relay — boot a peer-relay server on an ephemeral
 * port. The relay analogue of the mesh kit's {@link withRelay}.
 *
 * `createPeerRepoServer` takes a fixed port, which races in CI when two
 * runs collide. It also accepts a pre-built `WebSocketServer` override
 * "useful for tests that want to bind to a random port" — so we bind one to
 * port 0, read the OS-assigned port back, and hand it in. Storage goes to a
 * fresh temp dir per run so every script starts from cold disk, the relay
 * analogue of the mesh kit's fresh-profile guarantee.
 */

import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { WebSocketServer } from "ws";
import { createPeerRepoServer, type PeerRepoServer } from "../../../../src/peer";

export interface WithRepoServerResult {
  /** ws://127.0.0.1:<port> — pass to createPeerStateClient({ url }). */
  url: string;
  /** The running peer-relay server. Its `repo` is the always-on peer. */
  server: PeerRepoServer;
  /** Stop the server and delete its storage dir. Idempotent. */
  close: () => Promise<void>;
}

/**
 * Start a peer-relay server bound to a random free port with cold storage.
 */
export async function withRepoServer(): Promise<WithRepoServerResult> {
  const storageDir = mkdtempSync(join(tmpdir(), "polly-e2e-relay-"));

  const wss = new WebSocketServer({ port: 0, host: "127.0.0.1" });
  await new Promise<void>((resolve, reject) => {
    wss.once("listening", () => resolve());
    wss.once("error", reject);
  });
  const address = wss.address();
  if (typeof address === "string" || address === null) {
    throw new Error("withRepoServer: expected the server to be bound to a TCP address");
  }
  const port = address.port;

  // `port` is required by the type but ignored when `webSocketServer` is
  // supplied; pass the real one anyway so the value is coherent.
  const server = await createPeerRepoServer({
    port,
    webSocketServer: wss,
    storagePath: storageDir,
  });

  return {
    url: `ws://127.0.0.1:${port}`,
    server,
    close: async () => {
      await server.close();
      try {
        rmSync(storageDir, { recursive: true, force: true });
      } catch {
        // best effort
      }
    },
  };
}

/**
 * A one-line transport snapshot of a relay server, for convergence-timeout
 * diagnostics. `clients` is how many peers currently hold a socket to the hub
 * (the `ws` server's tracked connections); `docs` is how many documents the
 * hub's repo knows about. Pass `() => relayStats(relay.server)` as the
 * `context` of a convergence poller so a timeout answers the first question
 * worth asking — did the peers even reach the relay, and does it have the doc?
 */
export function relayStats(server: PeerRepoServer): string {
  const clients = server.webSocketServer.clients.size;
  const docs = Object.keys(server.repo.handles).length;
  return `clients=${clients} docs=${docs}`;
}
