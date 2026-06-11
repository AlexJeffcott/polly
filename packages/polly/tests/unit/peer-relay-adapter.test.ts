/**
 * Unit tests for createPeerStateClient — the one-call factory that builds a
 * Repo wired to the WebSocket peer-relay transport, with a reactive
 * connection-state signal and optional sign-only MeshNetworkAdapter wrapping.
 *
 * Mutation testing surfaced this module at 0% in the unit suite: it is
 * exercised only by the integration tests, which sit outside the mutation
 * kill-path. The factory hard-constructs a real WebSocketClientAdapter whose
 * socket would leak reconnect activity into the shared test process, so these
 * tests inject a fake adapter via `adapterFactory` and drive the lifecycle by
 * emitting events on it — entirely off the network.
 */
import { afterEach, describe, expect, test } from "bun:test";
import {
  NetworkAdapter,
  type PeerId,
  type StorageAdapterInterface,
} from "@automerge/automerge-repo/slim";
import type { WebSocketClientAdapter } from "@automerge/automerge-repo-network-websocket";
import { createPeerStateClient, type PeerStateClient } from "@/shared/lib/peer-relay-adapter";
import { generateSigningKeyPair } from "@/shared/lib/signing";

const URL = "ws://localhost:9/polly/peer";

/** A network adapter that opens no socket. Repo accepts it as a real adapter;
 * connect() reports ready immediately and send/disconnect are no-ops. */
class FakeAdapter extends NetworkAdapter {
  connect(peerId: PeerId): void {
    this.peerId = peerId;
    (this as unknown as { emit: (e: string, p?: unknown) => void }).emit("ready", {
      network: this,
    });
  }
  disconnect(): void {}
  send(): void {}
  isReady(): boolean {
    return true;
  }
  whenReady(): Promise<void> {
    return Promise.resolve();
  }
}

const clients: PeerStateClient[] = [];

function make(opts: Partial<Parameters<typeof createPeerStateClient>[0]> = {}): {
  client: PeerStateClient;
  adapter: FakeAdapter;
} {
  const adapter = new FakeAdapter();
  const client = createPeerStateClient({
    url: URL,
    adapterFactory: () => adapter as unknown as WebSocketClientAdapter,
    ...opts,
  });
  clients.push(client);
  return { client, adapter };
}

/** Emit a lifecycle event on the adapter, as the real one would at runtime. */
function fire(adapter: FakeAdapter, event: string, payload?: unknown): void {
  (adapter as unknown as { emit: (e: string, p?: unknown) => void }).emit(event, payload);
}

function makeKeyring() {
  return {
    identity: generateSigningKeyPair(),
    knownPeers: new Map<string, Uint8Array>(),
    documentKeys: new Map<string, Uint8Array>(),
    revokedPeers: new Set<string>(),
  };
}

afterEach(async () => {
  for (const c of clients) {
    try {
      await c.close();
    } catch {
      // best effort
    }
  }
  clients.length = 0;
});

describe("createPeerStateClient — construction", () => {
  test("returns a repo, a connecting signal, the adapter, and a close fn", () => {
    const { client, adapter } = make();
    expect(client.repo).toBeDefined();
    expect(client.connectionState.value).toBe("connecting");
    expect(client.adapter).toBe(adapter as unknown as WebSocketClientAdapter);
    expect(typeof client.close).toBe("function");
  });

  test("signEnabled is false by default", () => {
    expect(make().client.signEnabled).toBe(false);
  });

  test("uses the injected adapter factory instead of a real socket", () => {
    const { client, adapter } = make();
    expect(client.adapter).toBe(adapter as unknown as WebSocketClientAdapter);
  });
});

describe("createPeerStateClient — signing guard", () => {
  test("throws when sign is true but no keyring is supplied", () => {
    expect(() =>
      createPeerStateClient({
        url: URL,
        sign: true,
        adapterFactory: () => new FakeAdapter() as unknown as WebSocketClientAdapter,
      })
    ).toThrow(/requires a keyring/);
  });

  test("does not throw for sign:true with a keyring, and reports signEnabled", () => {
    expect(make({ sign: true, keyring: makeKeyring() }).client.signEnabled).toBe(true);
  });

  test("a keyring without sign does not enable signing", () => {
    expect(make({ keyring: makeKeyring() }).client.signEnabled).toBe(false);
  });
});

describe("createPeerStateClient — connection state transitions", () => {
  test("peer-candidate moves the signal to connected", () => {
    const { client, adapter } = make();
    fire(adapter, "peer-candidate", { peerId: "relay", peerMetadata: {} });
    expect(client.connectionState.value).toBe("connected");
  });

  test("peer-disconnected moves the signal to disconnected", () => {
    const { client, adapter } = make();
    fire(adapter, "peer-candidate", { peerId: "relay", peerMetadata: {} });
    expect(client.connectionState.value).toBe("connected");
    fire(adapter, "peer-disconnected", { peerId: "relay" });
    expect(client.connectionState.value).toBe("disconnected");
  });

  test("a socket close moves the signal to disconnected", () => {
    const { client, adapter } = make();
    fire(adapter, "peer-candidate", { peerId: "relay", peerMetadata: {} });
    fire(adapter, "close");
    expect(client.connectionState.value).toBe("disconnected");
  });
});

describe("createPeerStateClient — repo wiring", () => {
  // These assertions reach into Repo internals deliberately: the sign/keyring
  // adapter selection and the storage spread are otherwise only observable
  // through real network/storage behaviour (the integration tests' job).
  function repoNetworkAdapterName(client: PeerStateClient): string {
    const ns = (
      client.repo as unknown as {
        networkSubsystem?: { adapters?: Array<{ constructor: { name: string } }> };
      }
    ).networkSubsystem;
    return ns?.adapters?.[0]?.constructor.name ?? "(none)";
  }
  function repoHasStorage(client: PeerStateClient): boolean {
    return Boolean((client.repo as unknown as { storageSubsystem?: unknown }).storageSubsystem);
  }
  const fakeStorage: StorageAdapterInterface = {
    load: async () => undefined,
    save: async () => {},
    remove: async () => {},
    loadRange: async () => [],
    removeRange: async () => {},
  };

  test("wraps the adapter in a MeshNetworkAdapter only when signing", () => {
    expect(repoNetworkAdapterName(make().client)).toBe("FakeAdapter");
    expect(repoNetworkAdapterName(make({ sign: true, keyring: makeKeyring() }).client)).toBe(
      "MeshNetworkAdapter"
    );
  });

  test("gives the Repo a storage subsystem only when storage is supplied", () => {
    expect(repoHasStorage(make().client)).toBe(false);
    expect(repoHasStorage(make({ storage: fakeStorage }).client)).toBe(true);
  });
});

describe("createPeerStateClient — close", () => {
  test("close awaits the repo shutdown", async () => {
    const { client } = make();
    let shutdownCalls = 0;
    const realShutdown = client.repo.shutdown.bind(client.repo);
    client.repo.shutdown = async () => {
      shutdownCalls += 1;
      await realShutdown();
    };
    await client.close();
    expect(shutdownCalls).toBe(1);
  });
});
