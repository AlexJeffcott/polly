#!/usr/bin/env bun
/**
 * E2e: three-peer convergence over the peer-relay transport.
 *
 * The relay transport ($peerState over `createPeerStateClient` /
 * `createPeerRepoServer`) is a parallel public surface to the mesh, but the
 * only thing exercising it end to end is `peer-state-demo.ts` — a single
 * client talking to a single server. No committed artifact proves that
 * three peers converge through the relay, the relay analogue of the mesh
 * three-peer-convergence script.
 *
 * Scenario: one relay server, three cold clients. The flow exercises the
 * two propagation directions a real app depends on:
 *
 *   1. Client 1 authors a document through the documented `$peerState`
 *      entry point and writes a value. The change syncs to the relay
 *      server (the always-on peer).
 *   2. Clients 2 and 3 open the same document by id — standing in for
 *      whatever doc-discovery a real app layers on top, exactly as
 *      `peer-state-demo.ts` shares the id server-side — and the relay
 *      forwards client 1's state to both. All three converge on the write.
 *   3. Client 2 mutates the document. The change flows client-2 → server →
 *      clients 1 and 3. All three converge on the mutation.
 *
 * The second direction is the point: a relay that only pushed server→client
 * (or only forwarded the first writer) would pass step 2 and fail step 3.
 * Asserting convergence after a *non-authoring* client mutates proves the
 * relay forwards peer-to-peer through the hub.
 */

export const capability = "relay.three-peer-convergence" as const;

import type { DocHandle, DocumentId } from "@automerge/automerge-repo/slim";
import {
  $peerState,
  createPeerStateClient,
  type PeerStateClient,
  type VersionedDoc,
} from "../src/peer";
import {
  type RelayConvergenceTarget,
  waitForRelayConvergence,
  withRepoServer,
} from "../tools/test/src/e2e-relay";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

const CONNECT_TIMEOUT_MS = 5_000;

async function waitFor(predicate: () => boolean, timeoutMs: number, label: string): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (predicate()) return;
    await new Promise((r) => setTimeout(r, 25));
  }
  throw new Error(`timed out after ${timeoutMs}ms waiting for ${label}`);
}

/** Open a document by id, retrying until the relay has forwarded it or the
 *  timeout expires. `repo.find` rejects when the doc is not yet available on
 *  any connected peer; on a relay that means "not synced to the hub yet". */
async function findWithRetry(
  client: PeerStateClient,
  docId: DocumentId,
  timeoutMs: number
): Promise<DocHandle<Notes>> {
  const deadline = Date.now() + timeoutMs;
  let lastErr: unknown;
  while (Date.now() < deadline) {
    try {
      return await client.repo.find<Notes>(docId);
    } catch (err) {
      lastErr = err;
      await new Promise((r) => setTimeout(r, 50));
    }
  }
  throw new Error(
    `findWithRetry: document ${docId} not available within ${timeoutMs}ms (${lastErr instanceof Error ? lastErr.message : String(lastErr)})`
  );
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const relay = await withRepoServer();
  const relays = [relay];

  // Falsification gate: connect clients 2 and 3 to a SEPARATE relay so they
  // never share a hub with client 1. Cross-peer forwarding becomes
  // impossible and the script must FAIL at the open step — proof that the
  // shared relay is what the assertion actually depends on.
  const isolate = process.env["FALSIFY_ISOLATE_PEERS"] === "1";
  let othersUrl = relay.url;
  if (isolate) {
    const alt = await withRepoServer();
    relays.push(alt);
    othersUrl = alt.url;
  }

  const clients: PeerStateClient[] = [];
  const cleanup = async () => {
    for (const client of clients) {
      try {
        await client.close();
      } catch {
        // best effort
      }
    }
    for (const r of relays) await r.close();
  };

  try {
    for (let i = 1; i <= 3; i++) {
      const url = i === 1 ? relay.url : othersUrl;
      const client = createPeerStateClient({ url, retryInterval: 200 });
      clients.push(client);
    }
    const [c1, c2, c3] = clients;
    if (c1 === undefined || c2 === undefined || c3 === undefined) {
      throw new Error("test setup: expected three clients");
    }

    ctx.log("[e2e] three clients created; waiting for relay connections");
    await Promise.all(
      clients.map((client, i) =>
        waitFor(
          () => client.connectionState.value === "connected" && client.repo.peers.length > 0,
          CONNECT_TIMEOUT_MS,
          `client ${i + 1} connected`
        )
      )
    );

    // Client 1 authors through the documented $peerState entry point. Pass
    // the repo explicitly so the primitive resolves against this client's
    // repo without a module-global configurePeerState (three clients share
    // one process here; in production each is its own process).
    ctx.log('[e2e] client 1 authors $peerState("notes")');
    const notes = $peerState<Notes>("notes", { title: "", body: "" }, { repo: c1.repo });
    await notes.loaded;
    notes.value = { ...notes.value, title: "from peer-1" };
    const docId = notes.handle?.documentId;
    if (!docId) throw new Error("client 1 $peerState handle missing after loaded");

    // The relay must hold client 1's write before clients 2 and 3 can pull
    // it; wait for the server replica to show the title, mirroring the demo.
    ctx.log("[e2e] waiting for the write to reach the relay");
    await waitFor(
      () => {
        const handle = relay.server.repo.handles[docId];
        const doc: unknown = handle?.doc();
        return (
          typeof doc === "object" && doc !== null && "title" in doc && doc.title === "from peer-1"
        );
      },
      CONNECT_TIMEOUT_MS,
      "relay replica has client 1's write"
    );

    ctx.log("[e2e] clients 2 and 3 open the document; asserting convergence");
    const h2 = await findWithRetry(c2, docId, CONNECT_TIMEOUT_MS);
    const h3 = await findWithRetry(c3, docId, CONNECT_TIMEOUT_MS);

    const targets: RelayConvergenceTarget[] = [
      { peerId: "peer-1", read: () => notes.value.title },
      { peerId: "peer-2", read: () => h2.doc()?.title },
      { peerId: "peer-3", read: () => h3.doc()?.title },
    ];
    await waitForRelayConvergence(targets, (value) => value === "from peer-1");

    // Direction 2: a non-authoring client mutates. The change must flow
    // peer-2 → server → peers 1 and 3.
    ctx.log("[e2e] client 2 mutates; asserting peer-to-peer convergence through the relay");
    h2.change((doc) => {
      doc.body = "from peer-2";
    });
    const bodyTargets: RelayConvergenceTarget[] = [
      { peerId: "peer-1", read: () => notes.value.body },
      { peerId: "peer-2", read: () => h2.doc()?.body },
      { peerId: "peer-3", read: () => h3.doc()?.body },
    ];
    await waitForRelayConvergence(bodyTargets, (value) => value === "from peer-2");

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    await cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
