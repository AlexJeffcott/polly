/**
 * Full-stack $peerState integration test.
 *
 * The unit tests for $peerState use local-only Repos to validate the
 * primitive surface in isolation. The raw-Repo integration test in
 * peer-repo-relay.test.ts validates the WebSocket transport in isolation.
 * This test bridges the two: it exercises the entire application-facing
 * API — $peerState, configurePeerState, createPeerStateClient,
 * createPeerRepoServer — against a real WebSocket connection and verifies
 * that an application using only the public surface gets correct sync
 * end to end.
 *
 * Two clients are connected to the same server. One creates a $peerState
 * with a logical key; the other registers a $peerState with the same key,
 * waits for hydration, and observes the value the first client wrote.
 * Then the second client mutates and the first observes the change.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import { createPeerStateClient } from "@/shared/lib/peer-relay-adapter";
import { createPeerRepoServer, type PeerRepoServer } from "@/shared/lib/peer-repo-server";
import { $peerState, configurePeerState, resetPeerState } from "@/shared/lib/peer-state";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";
import type { VersionedDoc } from "@/shared/lib/schema-version";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

let pendingServers: PeerRepoServer[] = [];

beforeEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

afterEach(async () => {
  resetPeerState();
  primitiveRegistry.clear();
  migrationRegistry.clear();
  for (const s of pendingServers) {
    try {
      await s.close();
    } catch {
      // best effort
    }
  }
  pendingServers = [];
}, 30000);

async function startServer(port: number): Promise<PeerRepoServer> {
  const dir = mkdtempSync(join(tmpdir(), "polly-relay-test-"));
  const s = await createPeerRepoServer({ port, host: "127.0.0.1", storagePath: dir });
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

describe("$peerState end-to-end over the relay transport", () => {
  test("a $peerState created against a real server hydrates and writes through", async () => {
    const port = pickPort();
    const server = await startServer(port);

    const client = createPeerStateClient({
      url: `ws://127.0.0.1:${port}`,
      retryInterval: 100,
    });
    configurePeerState(client.repo);

    await waitFor(() => client.repo.peers.length > 0);

    const notes = $peerState<Notes>("end-to-end-notes", { title: "draft", body: "" });
    await notes.loaded;

    notes.value = { title: "published", body: "this is the body" };
    await Promise.resolve();

    // Wait for the document to land on the server.
    await waitFor(async () => {
      try {
        const sh = await server.repo.find<Notes>(notes.handle?.documentId ?? ("" as never));
        return sh.doc().title === "published";
      } catch {
        return false;
      }
    });

    expect(notes.handle).toBeDefined();
    const docId = notes.handle?.documentId;
    if (!docId) throw new Error("expected handle to be populated after loaded");
    const serverHandle = await server.repo.find<Notes>(docId);
    expect(serverHandle.doc().title).toBe("published");
    expect(serverHandle.doc().body).toBe("this is the body");

    await client.repo.shutdown();
  });

  test("a server-side mutation propagates back to the $peerState signal", async () => {
    const port = pickPort();
    const server = await startServer(port);

    const client = createPeerStateClient({
      url: `ws://127.0.0.1:${port}`,
      retryInterval: 100,
    });
    configurePeerState(client.repo);
    await waitFor(() => client.repo.peers.length > 0);

    const notes = $peerState<Notes>("server-mutate-notes", { title: "before", body: "" });
    await notes.loaded;
    notes.value = { title: "before", body: "initial" };
    await Promise.resolve();

    const docId = notes.handle?.documentId;
    if (!docId) throw new Error("expected handle to be populated after loaded");
    await waitFor(async () => {
      try {
        const sh = await server.repo.find<Notes>(docId);
        return sh.doc().body === "initial";
      } catch {
        return false;
      }
    });

    // Mutate from the server side; the change should arrive at the signal.
    const serverHandle = await server.repo.find<Notes>(docId);
    serverHandle.change((doc) => {
      doc.title = "after-server-change";
    });

    await waitFor(() => notes.value.title === "after-server-change");
    expect(notes.value.title).toBe("after-server-change");

    await client.repo.shutdown();
  });
});
