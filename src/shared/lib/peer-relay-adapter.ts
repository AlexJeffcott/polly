/**
 * peer-relay-adapter — Phase 1 client helper for connecting a Polly $peerState
 * application to an Automerge-Repo relay server over WebSocket.
 *
 * The Phase 0 base $crdtState and the Phase 1 $peerState wrapper both consume
 * a caller-supplied `Repo` via `configurePeerState`. This module provides the
 * one-call factory that builds a Repo wired to the relay transport: a
 * `WebSocketClientAdapter` from `@automerge/automerge-repo-network-websocket`
 * pointed at the server URL, an `IndexedDBStorageAdapter` for client-side
 * persistence, and a Polly-shaped connection-state signal that the application
 * can render as a diagnostic UI or feed into reconnection logic.
 *
 * The mirror server-side factory is in {@link peer-repo-server}.
 *
 * @example
 * ```ts
 * import { configurePeerState } from "@fairfox/polly";
 * import { createPeerStateClient } from "@fairfox/polly";
 *
 * const { repo, connectionState } = await createPeerStateClient({
 *   url: "wss://yourapp.example.com/polly/peer",
 * });
 * configurePeerState(repo);
 *
 * // connectionState is a Signal<"connecting" | "connected" | "disconnected">
 * ```
 */

import { Repo } from "@automerge/automerge-repo";
import { WebSocketClientAdapter } from "@automerge/automerge-repo-network-websocket";
import { type Signal, signal } from "@preact/signals";

export type PeerRelayConnectionState = "connecting" | "connected" | "disconnected";

export interface CreatePeerStateClientOptions {
  /** WebSocket URL of the Polly peer-relay server. Use `ws://` for local
   * development and `wss://` for any deployment that terminates TLS. */
  url: string;
  /** Reconnect interval in milliseconds. Defaults to Automerge-Repo's own
   * default (5 seconds at the time of writing). */
  retryInterval?: number;
  /** Optional storage adapter. Applications running in a browser typically
   * pass an `IndexedDBStorageAdapter`; tests pass nothing for a local-only
   * Repo. The default is no storage, which keeps the client purely in-memory. */
  storage?: ConstructorParameters<typeof Repo>[0] extends infer C
    ? C extends { storage?: infer S }
      ? S
      : never
    : never;
}

export interface PeerStateClient {
  /** A configured Repo backed by the WebSocket relay. Pass to
   * {@link configurePeerState}. */
  repo: Repo;
  /** Reactive connection state. Updates as the underlying WebSocket opens,
   * closes, and reconnects. */
  connectionState: Signal<PeerRelayConnectionState>;
  /** The underlying network adapter, exposed for advanced use. */
  adapter: WebSocketClientAdapter;
  /** Disconnect from the relay and tear down the Repo. Awaiting the
   * returned promise drains the Repo's subsystems cleanly. */
  close: () => Promise<void>;
}

/**
 * Construct a Polly-flavoured client for the peer-relay transport.
 *
 * The returned object includes the Repo, a connection-state signal, the
 * underlying network adapter, and a close function. Production code typically
 * passes the Repo to {@link configurePeerState} and renders the connection
 * state somewhere visible.
 */
export function createPeerStateClient(options: CreatePeerStateClientOptions): PeerStateClient {
  const adapter = new WebSocketClientAdapter(options.url, options.retryInterval);
  const connectionState = signal<PeerRelayConnectionState>("connecting");

  // The WebSocketClientAdapter is itself an EventEmitter (via Automerge's
  // NetworkAdapter base class) and emits 'peer-candidate' / 'peer-disconnected'
  // events. We track the simpler open/close lifecycle by listening to those.
  adapter.on("peer-candidate", () => {
    connectionState.value = "connected";
  });
  adapter.on("peer-disconnected", () => {
    connectionState.value = "disconnected";
  });
  adapter.on("close", () => {
    connectionState.value = "disconnected";
  });

  const repo = new Repo({
    network: [adapter],
    ...(options.storage !== undefined && { storage: options.storage }),
  });

  return {
    repo,
    connectionState,
    adapter,
    // Delegate to repo.shutdown() rather than calling adapter.disconnect()
    // directly. Automerge-Repo's WebSocketClientAdapter has an internal
    // assertion that fires if disconnect() is called twice, and the Repo's
    // shutdown also iterates network adapters and disconnects each. Routing
    // tear-down through shutdown() means there is one disconnect path.
    close: async () => {
      await repo.shutdown();
    },
  };
}
