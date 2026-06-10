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
import { type AddressInfo, WebSocketServer } from "ws";
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
  const address = wss.address() as AddressInfo;
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
