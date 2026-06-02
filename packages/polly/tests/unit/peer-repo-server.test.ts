/**
 * Tests for peer-repo-server.ts — the server-side $peerState factory.
 *
 * Two surfaces are covered:
 *
 *  - `listNodeFSDocumentIds`, the storage-tree walker that recovers the
 *    document list for `sweepSealed`. Driven against real temp directories
 *    laid out in the NodeFS two-level shard shape (it uses only node
 *    built-ins, so it runs anywhere).
 *
 *  - `createPeerRepoServer` end to end against the real automerge-repo / ws
 *    stack, using the `webSocketServer` injection seam (and `port: 0`) so no
 *    fixed port is bound. The timing-bound sync behaviour — storageId-gated
 *    handshakes, background flush, multi-peer relay — stays in the
 *    integration suite (`tests/integration/peer-repo-relay.test.ts`).
 */

import { afterEach, describe, expect, test } from "bun:test";
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  createPeerRepoServer,
  listNodeFSDocumentIds,
  type PeerRepoServer,
} from "@/shared/lib/peer-repo-server";

// ---------------------------------------------------------------------------
// listNodeFSDocumentIds
// ---------------------------------------------------------------------------

function freshDir(): string {
  return mkdtempSync(join(tmpdir(), "polly-peer-server-"));
}

/** Lay down a document the way NodeFSStorageAdapter shards it: the first two
 * characters of the documentId are the shard directory, the remainder is a
 * directory beneath it. Returns the documentId. */
function writeDocDir(base: string, documentId: string): string {
  const shard = documentId.slice(0, 2);
  const rest = documentId.slice(2);
  mkdirSync(join(base, shard, rest), { recursive: true });
  return documentId;
}

describe("listNodeFSDocumentIds", () => {
  test("returns [] for a storage directory that has never been written", async () => {
    expect(await listNodeFSDocumentIds(join(tmpdir(), "polly-does-not-exist-xyz"))).toEqual([]);
  });

  test("returns [] for an empty storage directory", async () => {
    expect(await listNodeFSDocumentIds(freshDir())).toEqual([]);
  });

  test("recovers a single sharded documentId", async () => {
    const base = freshDir();
    const id = writeDocDir(base, "abcdef123456");
    expect(await listNodeFSDocumentIds(base)).toEqual([id]);
  });

  test("recovers every document across multiple shards", async () => {
    const base = freshDir();
    const ids = [
      writeDocDir(base, "abcdef0001"),
      writeDocDir(base, "abzzzz0002"),
      writeDocDir(base, "qrwxyz0003"),
    ];
    expect((await listNodeFSDocumentIds(base)).sort()).toEqual(ids.sort());
  });

  test("recovers two documents sharing one shard prefix", async () => {
    const base = freshDir();
    const ids = [writeDocDir(base, "ababcd0001"), writeDocDir(base, "abefgh0002")];
    expect((await listNodeFSDocumentIds(base)).sort()).toEqual(ids.sort());
  });

  test("skips non-directory entries inside a shard (e.g. stray files)", async () => {
    const base = freshDir();
    const id = writeDocDir(base, "abcdef0001");
    // A stray file sitting alongside the document directory in the same shard.
    writeFileSync(join(base, "ab", "stray-file"), "x");
    expect(await listNodeFSDocumentIds(base)).toEqual([id]);
  });

  test("skips flat files at the storage root (e.g. the storage-adapter-id)", async () => {
    const base = freshDir();
    const id = writeDocDir(base, "abcdef0001");
    // NodeFSStorageAdapter writes its own id as a flat file at the root;
    // readdir on it throws ENOTDIR, which the walker swallows.
    writeFileSync(join(base, "storage-adapter-id"), "some-id");
    expect(await listNodeFSDocumentIds(base)).toEqual([id]);
  });

  test("propagates errors that are not ENOENT", async () => {
    // A path whose parent is a file, not a directory: readdir rejects with
    // ENOTDIR, which is not ENOENT and must propagate rather than yield [].
    const base = freshDir();
    const filePath = join(base, "a-file");
    writeFileSync(filePath, "x");
    await expect(listNodeFSDocumentIds(join(filePath, "under-a-file"))).rejects.toThrow();
  });
});

// ---------------------------------------------------------------------------
// createPeerRepoServer (real stack, no fixed port)
// ---------------------------------------------------------------------------

describe("createPeerRepoServer", () => {
  let server: PeerRepoServer | undefined;
  const extraCleanup: Array<() => void> = [];

  afterEach(async () => {
    if (server) {
      await server.close();
      server = undefined;
    }
    for (const fn of extraCleanup.splice(0)) {
      try {
        fn();
      } catch {
        /* best effort */
      }
    }
  }, 30000);

  test("binds an OS-assigned port (port 0) on the requested host and wires the server", async () => {
    const storagePath = freshDir();
    server = await createPeerRepoServer({ port: 0, host: "127.0.0.1", storagePath });
    expect(server.repo).toBeDefined();
    expect(server.webSocketServer).toBeDefined();
    expect(server.adapter).toBeDefined();
    expect(server.storage).toBeDefined();
    expect(typeof server.close).toBe("function");
    expect(typeof server.sweepSealed).toBe("function");
    // The `host` option is threaded through to the bound address — a host of
    // 127.0.0.1 binds the loopback interface, not all interfaces.
    const address = (server.webSocketServer.address() as { address: string }).address;
    expect(address).toBe("127.0.0.1");
    // The storagePath is handed to the NodeFS adapter verbatim.
    expect((server.storage as unknown as { baseDirectory: string }).baseDirectory).toBe(
      storagePath
    );
  });

  test("defaults the storage path to automerge-repo-data when none is given", async () => {
    server = await createPeerRepoServer({ port: 0, host: "127.0.0.1" });
    expect((server.storage as unknown as { baseDirectory: string }).baseDirectory).toBe(
      "automerge-repo-data"
    );
    // storageId() created the directory relative to cwd; remove it on teardown.
    extraCleanup.push(() => rmSync("automerge-repo-data", { recursive: true, force: true }));
  });

  test("rejects when the requested port is already in use", async () => {
    const { WebSocketServer } = await import("ws");
    const blocker = new WebSocketServer({ port: 0, host: "127.0.0.1" });
    await new Promise<void>((resolve) => blocker.once("listening", () => resolve()));
    const port = (blocker.address() as { port: number }).port;
    extraCleanup.push(() => blocker.close());
    // The factory wires `created.once("error", reject)`; a second bind to the
    // same port emits EADDRINUSE, which must reject the returned promise
    // rather than hang.
    await expect(createPeerRepoServer({ port, host: "127.0.0.1" })).rejects.toThrow();
  });

  test("uses the injected webSocketServer instead of binding a port", async () => {
    const { WebSocketServer } = await import("ws");
    const injected = new WebSocketServer({ port: 0 });
    const storagePath = freshDir();
    server = await createPeerRepoServer({ port: 9999, storagePath, webSocketServer: injected });
    // The returned server exposes the very instance we handed in — the port
    // option was ignored.
    expect(server.webSocketServer).toBe(injected);
  });

  test("sweepSealed enumerates storage and reports nothing for an empty server", async () => {
    const storagePath = freshDir();
    server = await createPeerRepoServer({ port: 0, host: "127.0.0.1", storagePath });
    const result = await server.sweepSealed({
      isSealed: () => undefined,
      olderThan: 0,
      dryRun: true,
    });
    expect(result).toEqual({ swept: [], kept: [], dryRun: true });
  });

  test("sweepSealed echoes the dryRun flag it was called with", async () => {
    const storagePath = freshDir();
    server = await createPeerRepoServer({ port: 0, host: "127.0.0.1", storagePath });
    const result = await server.sweepSealed({ isSealed: () => undefined, olderThan: 1000 });
    expect(result.dryRun).toBe(false);
  });

  test("close terminates still-open client sockets", async () => {
    const storagePath = freshDir();
    const created = await createPeerRepoServer({ port: 0, host: "127.0.0.1", storagePath });
    const { WebSocket } = await import("ws");
    const port = (created.webSocketServer.address() as { port: number }).port;
    const client = new WebSocket(`ws://127.0.0.1:${port}`);
    await new Promise<void>((resolve, reject) => {
      client.once("open", () => resolve());
      client.once("error", reject);
    });
    expect(created.webSocketServer.clients.size).toBe(1);
    const clientClosed = new Promise<void>((resolve) => client.once("close", () => resolve()));
    await created.close();
    // terminate() forces the connected socket closed during teardown.
    await clientClosed;
    expect(created.webSocketServer.clients.size).toBe(0);
    server = undefined;
  });

  test("close tears down the WebSocket server and is safe to await", async () => {
    const { WebSocketServer } = await import("ws");
    const injected = new WebSocketServer({ port: 0 });
    const storagePath = freshDir();
    const created = await createPeerRepoServer({ port: 0, storagePath, webSocketServer: injected });
    let closed = false;
    injected.on("close", () => {
      closed = true;
    });
    await created.close();
    // wss.close() was invoked during teardown.
    await new Promise((r) => setTimeout(r, 50));
    expect(closed).toBe(true);
    // server already torn down; nothing left for afterEach to close.
    server = undefined;
  });
});
