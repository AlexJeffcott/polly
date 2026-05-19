import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Repo } from "@automerge/automerge-repo";
import { WebSocketClientAdapter } from "@automerge/automerge-repo-network-websocket";
import { createPeerRepoServer, type PeerRepoServer } from "@/shared/lib/peer-repo-server";

type Doc = {
  title: string;
  count: number;
};

let server: PeerRepoServer | undefined;
let storageDir: string | undefined;

beforeEach(() => {
  storageDir = mkdtempSync(join(tmpdir(), "polly-peer-test-"));
});

afterEach(async () => {
  if (server) {
    await server.close();
    server = undefined;
  }
  // Storage directories are left in tmpdir; the OS prunes them. Awaiting an
  // explicit rmSync here races the Repo's background flush and breaks tests
  // that wrote during their final assertions.
  storageDir = undefined;
}, 30000);

/**
 * Wait until a predicate becomes true or the timeout elapses. Polls every
 * 25ms. Used to wait for sync to converge between two peers.
 */
async function waitFor(
  predicate: () => boolean | Promise<boolean>,
  timeoutMs = 5000
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return;
    await new Promise((r) => setTimeout(r, 25));
  }
  throw new Error(`Timed out after ${timeoutMs}ms waiting for predicate`);
}

/** Pick an arbitrary high port for the test server. */
function pickPort(): number {
  // Random in 30000-39999 — high enough to avoid common dev ports, low
  // enough to stay below ephemeral range collisions in CI.
  return 30000 + Math.floor(Math.random() * 10000);
}

describe("peer-repo-relay integration", () => {
  test("server starts on the configured port and accepts a client", async () => {
    const port = pickPort();
    server = await createPeerRepoServer({ port, host: "127.0.0.1", storagePath: storageDir });
    expect(server.repo).toBeDefined();
    expect(server.webSocketServer).toBeDefined();

    // Connect a client and verify the adapter reaches the connected state.
    const client = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${port}`)],
    });

    await waitFor(() => client.peers.length > 0);
    expect(client.peers.length).toBeGreaterThan(0);

    await client.shutdown();
  });

  test("a document created on the client syncs to the server", async () => {
    const port = pickPort();
    server = await createPeerRepoServer({ port, host: "127.0.0.1", storagePath: storageDir });

    const client = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${port}`)],
    });
    await waitFor(() => client.peers.length > 0);

    const clientHandle = client.create<Doc>({ title: "from client", count: 1 });
    await clientHandle.whenReady();
    const docId = clientHandle.documentId;

    // Wait for the document to appear on the server side.
    await waitFor(async () => {
      try {
        const serverHandle = await server!.repo.find<Doc>(docId);
        await serverHandle.whenReady();
        return serverHandle.doc().title === "from client";
      } catch {
        return false;
      }
    });

    const serverHandle = await server.repo.find<Doc>(docId);
    expect(serverHandle.doc().title).toBe("from client");
    expect(serverHandle.doc().count).toBe(1);

    await client.shutdown();
  });

  test("a document created on the server syncs to the client", async () => {
    const port = pickPort();
    server = await createPeerRepoServer({ port, host: "127.0.0.1", storagePath: storageDir });

    const serverHandle = server.repo.create<Doc>({ title: "from server", count: 7 });
    await serverHandle.whenReady();
    const docId = serverHandle.documentId;

    const client = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${port}`)],
    });
    await waitFor(() => client.peers.length > 0);

    const clientHandle = await client.find<Doc>(docId);
    await waitFor(() => clientHandle.doc().title === "from server");
    expect(clientHandle.doc().title).toBe("from server");
    expect(clientHandle.doc().count).toBe(7);

    await client.shutdown();
  });

  test("a write on one side propagates to the other after both are connected", async () => {
    const port = pickPort();
    server = await createPeerRepoServer({ port, host: "127.0.0.1", storagePath: storageDir });

    const client = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${port}`)],
    });
    await waitFor(() => client.peers.length > 0);

    const clientHandle = client.create<Doc>({ title: "shared", count: 0 });
    await clientHandle.whenReady();
    const docId = clientHandle.documentId;

    // Wait for the server to learn about the doc.
    await waitFor(async () => {
      try {
        const sh = await server!.repo.find<Doc>(docId);
        await sh.whenReady();
        return true;
      } catch {
        return false;
      }
    });

    // Mutate on the server side; the change should propagate back to the client.
    const serverHandle = await server.repo.find<Doc>(docId);
    serverHandle.change((doc) => {
      doc.count = 42;
    });

    await waitFor(() => clientHandle.doc().count === 42);
    expect(clientHandle.doc().count).toBe(42);

    await client.shutdown();
  });
});
