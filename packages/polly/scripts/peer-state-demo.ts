#!/usr/bin/env bun
/**
 * Runnable demo for RFC-041 Phase 1 — $peerState over the relay transport.
 *
 * This script boots a real Polly peer-repo server on a temporary port,
 * connects a real Polly peer-state client to it, registers a $peerState
 * primitive against the configured Repo, writes to it, reads it back
 * through the server to confirm the round trip, mutates it from the
 * server side to show bidirectional sync, and tears everything down
 * cleanly. It exists as a living end-to-end smoke test for the public
 * API and as a minimal reference for applications.
 *
 * Run with:
 *
 *   bun run scripts/peer-state-demo.ts
 *
 * Expected output (truncated):
 *
 *   [demo] starting peer-repo server on port 34321 with storage /tmp/…
 *   [demo] connecting client to ws://127.0.0.1:34321
 *   [demo] client connected, peers=1
 *   [demo] registering $peerState("notes", …)
 *   [demo] initial value: { title: "", body: "" }
 *   [demo] hydrated, writing new value
 *   [demo] server-side handle now shows: { title: "from client", body: "…" }
 *   [demo] mutating from the server side, waiting for client signal update
 *   [demo] client signal now shows: { title: "from client", body: "from server" }
 *   [demo] shutdown
 */

import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  $peerState,
  configurePeerState,
  createPeerRepoServer,
  createPeerStateClient,
  resetPeerState,
  type VersionedDoc,
} from "@/peer";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

function pickPort(): number {
  return 34000 + Math.floor(Math.random() * 1000);
}

async function waitFor(
  predicate: () => boolean | Promise<boolean>,
  timeoutMs = 3000
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return;
    await new Promise((r) => setTimeout(r, 20));
  }
  throw new Error(`Timed out after ${timeoutMs}ms`);
}

async function main(): Promise<void> {
  const port = pickPort();
  const storageDir = mkdtempSync(join(tmpdir(), "polly-demo-server-"));
  console.log(`[demo] starting peer-repo server on port ${port} with storage ${storageDir}`);
  const server = await createPeerRepoServer({
    port,
    host: "127.0.0.1",
    storagePath: storageDir,
  });

  console.log(`[demo] connecting client to ws://127.0.0.1:${port}`);
  const client = createPeerStateClient({
    url: `ws://127.0.0.1:${port}`,
    retryInterval: 200,
  });
  configurePeerState(client.repo);

  await waitFor(() => client.repo.peers.length > 0);
  console.log(`[demo] client connected, peers=${client.repo.peers.length}`);

  console.log(`[demo] registering $peerState("notes", …)`);
  const notes = $peerState<Notes>("notes", { title: "", body: "" });
  console.log(`[demo] initial value: ${JSON.stringify(notes.value)}`);

  await notes.loaded;
  console.log(`[demo] hydrated, writing new value`);
  notes.value = { title: "from client", body: "written on the client side" };
  await Promise.resolve();

  // Wait for the document to land on the server's replica.
  const docId = notes.handle?.documentId;
  if (!docId) throw new Error("handle missing after loaded");
  await waitFor(async () => {
    try {
      const sh = await server.repo.find<Notes>(docId);
      return sh.doc().title === "from client";
    } catch {
      return false;
    }
  });
  const serverHandle = await server.repo.find<Notes>(docId);
  console.log(`[demo] server-side handle now shows: ${JSON.stringify(serverHandle.doc())}`);

  console.log(`[demo] mutating from the server side, waiting for client signal update`);
  serverHandle.change((doc) => {
    doc.body = "from server";
  });
  await waitFor(() => notes.value.body === "from server");
  console.log(`[demo] client signal now shows: ${JSON.stringify(notes.value)}`);

  console.log(`[demo] shutdown`);
  await client.close();
  await server.close();
  resetPeerState();
}

main().catch((err) => {
  console.log("[demo] failed:", err);
  process.exit(1);
});
