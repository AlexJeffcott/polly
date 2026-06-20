/**
 * Step bindings for the mesh `sync.feature` — the one scenario that crosses the
 * real device/network boundary.
 *
 * Unlike the in-process todo world (createBackground + driveBus), this world is
 * a *page driver*: `defineWorld.create()` boots a real signalling relay and two
 * cold browser peers through the documented `createMeshClient` bootstrap (the
 * e2e-mesh kit), and the steps drive Puppeteer pages plus `waitForConvergence`.
 *
 * The browsers and relay outlive any single scenario, so they live at module
 * scope — NOT in `world.vars`, which the runner wipes before every scenario as
 * per-scenario scratch. `teardown` closes them so the runner exits cleanly. The
 * bus/signals a normal world carries are absent here (a mesh scenario observes
 * two browsers' DOM, not in-process signals), so `bus` throws if touched.
 */
import { defineStep, defineWorld } from "../../tools/bdd/src/index.ts";
import type { BusLike, World } from "../../tools/bdd/src/types.ts";
import {
  knownPeersFor,
  type LaunchedPeer,
  launchPeer,
  prebakeKeyringSet,
  type ServeConsumerResult,
  serveConsumer,
  type WithRelayResult,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../../tools/test/src/e2e-mesh/index.ts";

interface MeshContext {
  relay: WithRelayResult;
  servers: ServeConsumerResult[];
  peers: LaunchedPeer[];
}

const CONVERGE_TIMEOUT_MS = 20_000;
const SETTLE_MS = 2_000;

/** Process-scoped mesh resources — survive the per-scenario `world.vars` wipe. */
let mesh: MeshContext | null = null;

function ctx(): MeshContext {
  if (!mesh) throw new Error("mesh world not created — defineWorld.create() did not run");
  return mesh;
}

function peerNamed(label: "A" | "B"): LaunchedPeer {
  const peer = ctx().peers[label === "A" ? 0 : 1];
  if (!peer) throw new Error(`device ${label} was not launched`);
  return peer;
}

/** Block until every peer's rendered list contains `value`. */
function awaitItem(value: string): Promise<void> {
  return waitForConvergence(ctx().peers, (snapshot) => snapshot.items.includes(value), {
    timeoutMs: CONVERGE_TIMEOUT_MS,
  });
}

/** A mesh scenario drives pages, not an in-process bus — guard against misuse. */
const pageDrivenBus: BusLike = {
  send() {
    throw new Error("the mesh world drives browser pages; it has no in-process bus");
  },
};

defineWorld({
  async create(): Promise<World> {
    const relay = await withRelay();
    const set = prebakeKeyringSet(["device-a", "device-b"]);
    const servers: ServeConsumerResult[] = [];
    const peers: LaunchedPeer[] = [];

    for (const peer of set.peers) {
      const server = await serveConsumer({
        bootstrap: {
          peerId: peer.peerId,
          signalingUrl: relay.url,
          identitySecretKeyB64: peer.identitySecretKeyB64,
          knownPeers: knownPeersFor(set, peer.peerId),
          docKeyB64: set.docKeyB64,
        },
      });
      servers.push(server);
      peers.push(await launchPeer({ peerId: peer.peerId, consumerUrl: server.url }));
    }

    mesh = { relay, servers, peers };
    return { bus: pageDrivenBus, signals: {}, vars: {} };
  },

  reset() {
    // Single scenario, cold from create(); nothing to reset between scenarios.
    // (A second scenario would need per-scenario peers or a doc reset.)
  },

  async teardown() {
    if (!mesh) return;
    for (const peer of mesh.peers) await peer.close();
    for (const server of mesh.servers) await server.close();
    await mesh.relay.close();
    mesh = null;
  },
});

defineStep({
  pattern: "two devices are connected to the same mesh",
  given: async () => {
    // create() already launched and paired both peers; confirm the WebRTC mesh
    // is up, then let the pairwise link settle before the first write.
    await waitForMeshConnected(ctx().peers, { timeoutMs: 15_000 });
    await new Promise((r) => setTimeout(r, SETTLE_MS));
  },
});

defineStep({
  pattern: "device A adds the todo {string}",
  when: async (_world, value) => {
    const a = peerNamed("A");
    await a.page.type("[data-e2e='add-item-input']", value);
    await a.page.click("[data-e2e='add-item-button']");
  },
});

defineStep({
  pattern: "device B adds the todo {string}",
  when: async (_world, value) => {
    const b = peerNamed("B");
    await b.page.type("[data-e2e='add-item-input']", value);
    await b.page.click("[data-e2e='add-item-button']");
  },
});

defineStep({
  pattern: "device B sees the todo {string}",
  then: (_world, value) => awaitItem(value),
});

defineStep({
  pattern: "device A sees the todo {string}",
  then: (_world, value) => awaitItem(value),
});

defineStep({
  pattern: "both devices show {int} todos",
  then: async (_world, count) => {
    const n = Number(count);
    await waitForConvergence(ctx().peers, (snapshot) => snapshot.items.length === n, {
      timeoutMs: CONVERGE_TIMEOUT_MS,
    });
  },
});
