/**
 * Resilience integration test for the Phase 1 peer-relay transport.
 *
 * The middle resilience tier ($peerState) promises that "any device is a
 * backup": if the server loses its storage, any reconnecting client whose
 * local replica still holds the document can repopulate the server through
 * the normal sync protocol. This test exercises that recovery path end to
 * end.
 *
 * Scenario:
 *   1. Server A starts with persistent NodeFS storage on dir-server-1.
 *   2. Client A starts with persistent NodeFS storage on dir-client and
 *      connects to Server A.
 *   3. Client A creates a document and waits for it to sync to Server A.
 *      Server A flushes the document to dir-server-1.
 *   4. Both server and client are torn down. dir-server-1 is left intact
 *      but Server A is gone.
 *   5. Server B starts with a *fresh* storage path (dir-server-2). This
 *      simulates total data loss: Server B has no record of the document.
 *   6. Client B starts with the *same* storage path as Client A
 *      (dir-client) so that its local replica still holds the document
 *      from the previous session, and connects to Server B.
 *   7. Client B's Repo, on hydration from disk, sends sync messages to
 *      Server B. Server B receives the document and stores it.
 *   8. Verify Server B can find the document by id and that its contents
 *      match what Client A originally wrote.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { type DocumentId, Repo } from "@automerge/automerge-repo";
import { WebSocketClientAdapter } from "@automerge/automerge-repo-network-websocket";
import { NodeFSStorageAdapter } from "@automerge/automerge-repo-storage-nodefs";
import { createPeerRepoServer, type PeerRepoServer } from "@/shared/lib/peer-repo-server";

type Doc = {
  title: string;
  count: number;
};

let pendingServers: PeerRepoServer[] = [];

afterEach(async () => {
  for (const s of pendingServers) {
    try {
      await s.close();
    } catch {
      // best effort
    }
  }
  pendingServers = [];
}, 30000);

async function startServer(port: number, storagePath: string): Promise<PeerRepoServer> {
  const s = await createPeerRepoServer({ port, host: "127.0.0.1", storagePath });
  pendingServers.push(s);
  return s;
}

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

function pickPort(): number {
  return 30000 + Math.floor(Math.random() * 10000);
}

describe("$peerState resilience", () => {
  test("server can recover document state from a reconnecting client after data loss", async () => {
    const portA = pickPort();
    const portB = pickPort();
    const serverDirA = mkdtempSync(join(tmpdir(), "polly-server-a-"));
    const serverDirB = mkdtempSync(join(tmpdir(), "polly-server-b-"));
    const clientDir = mkdtempSync(join(tmpdir(), "polly-client-"));

    // ─── Phase 1: client creates a doc and syncs to server A ────────────────
    const serverA = await startServer(portA, serverDirA);

    const clientA = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${portA}`, 100)],
      storage: new NodeFSStorageAdapter(clientDir),
    });
    await waitFor(() => clientA.peers.length > 0);

    const handleA = clientA.create<Doc>({ title: "important note", count: 42 });
    await handleA.whenReady();
    const docId: DocumentId = handleA.documentId;

    // Wait for server A to learn about the document.
    await waitFor(async () => {
      try {
        const sh = await serverA.repo.find<Doc>(docId);
        await sh.whenReady();
        return sh.doc().title === "important note";
      } catch {
        return false;
      }
    });

    // Force the server to flush the document to disk before tearing it down,
    // so dir-server-1 contains real persisted state. Not strictly needed for
    // the recovery path (we are simulating loss anyway) but it confirms the
    // server actually had the data when it died.
    await serverA.repo.flush([docId]);

    // ─── Tear down server A and client A ─────────────────────────────────────
    await clientA.shutdown();
    await serverA.close();
    pendingServers = pendingServers.filter((s) => s !== serverA);

    // Brief settle so the OS releases the listening socket.
    await new Promise((r) => setTimeout(r, 100));

    // ─── Phase 2: fresh server B with a fresh storage path = data loss ──────
    const serverB = await startServer(portB, serverDirB);

    // Confirm server B starts with no knowledge of the document. find() will
    // hang waiting for a peer that has the doc, so we just check the handle
    // cache directly.
    expect(serverB.repo.handles[docId]).toBeUndefined();

    // ─── Phase 3: client B reconnects with the same client storage ──────────
    const clientB = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${portB}`, 100)],
      storage: new NodeFSStorageAdapter(clientDir),
    });
    await waitFor(() => clientB.peers.length > 0);

    // Ask client B to find the document by id. It should hydrate from local
    // storage (the same NodeFS dir client A used) and immediately know about
    // it. The Automerge sync protocol then pushes the document to server B.
    const handleB = await clientB.find<Doc>(docId);
    await handleB.whenReady();
    expect(handleB.doc().title).toBe("important note");
    expect(handleB.doc().count).toBe(42);

    // Wait for server B to receive the document via sync from client B.
    await waitFor(async () => {
      try {
        const sh = await serverB.repo.find<Doc>(docId);
        await sh.whenReady();
        return sh.doc().title === "important note";
      } catch {
        return false;
      }
    });

    const recoveredOnServer = await serverB.repo.find<Doc>(docId);
    expect(recoveredOnServer.doc().title).toBe("important note");
    expect(recoveredOnServer.doc().count).toBe(42);

    await clientB.shutdown();
  });

  test("a write on the recovered server propagates back to the client", async () => {
    const portA = pickPort();
    const portB = pickPort();
    const serverDirA = mkdtempSync(join(tmpdir(), "polly-server-a-"));
    const serverDirB = mkdtempSync(join(tmpdir(), "polly-server-b-"));
    const clientDir = mkdtempSync(join(tmpdir(), "polly-client-"));

    // Set up a doc on server A and client A.
    const serverA = await startServer(portA, serverDirA);
    const clientA = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${portA}`, 100)],
      storage: new NodeFSStorageAdapter(clientDir),
    });
    await waitFor(() => clientA.peers.length > 0);

    const handleA = clientA.create<Doc>({ title: "evolving doc", count: 1 });
    await handleA.whenReady();
    const docId = handleA.documentId;
    await waitFor(async () => {
      try {
        const sh = await serverA.repo.find<Doc>(docId);
        return sh.doc().title === "evolving doc";
      } catch {
        return false;
      }
    });
    await serverA.repo.flush([docId]);

    // Lose server A.
    await clientA.shutdown();
    await serverA.close();
    pendingServers = pendingServers.filter((s) => s !== serverA);
    await new Promise((r) => setTimeout(r, 100));

    // Bring up server B and client B.
    const serverB = await startServer(portB, serverDirB);
    const clientB = new Repo({
      network: [new WebSocketClientAdapter(`ws://127.0.0.1:${portB}`, 100)],
      storage: new NodeFSStorageAdapter(clientDir),
    });
    await waitFor(() => clientB.peers.length > 0);

    const handleB = await clientB.find<Doc>(docId);
    await handleB.whenReady();

    // Wait for the doc to land on server B via sync.
    await waitFor(async () => {
      try {
        const sh = await serverB.repo.find<Doc>(docId);
        return sh.doc().title === "evolving doc";
      } catch {
        return false;
      }
    });

    // Now mutate on server B and verify the change propagates back to client B.
    const serverHandleB = await serverB.repo.find<Doc>(docId);
    serverHandleB.change((doc) => {
      doc.count = 99;
    });

    await waitFor(() => handleB.doc().count === 99);
    expect(handleB.doc().count).toBe(99);

    await clientB.shutdown();
  });
});
