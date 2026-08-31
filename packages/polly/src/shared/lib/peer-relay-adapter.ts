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

import { type NetworkAdapterInterface, Repo } from "@automerge/automerge-repo/slim";
import { WebSocketClientAdapter } from "@automerge/automerge-repo-network-websocket";
import { type Signal, signal } from "@preact/signals";
import { type MeshKeyring, MeshNetworkAdapter } from "./mesh-network-adapter";

export type PeerRelayConnectionState = "connecting" | "connected" | "disconnected";

export interface CreatePeerStateClientOptions {
  /** WebSocket URL of the Polly peer-relay server. Use the unencrypted scheme
   * (`ws:` + `//`) for local development; `wss://` is required for any
   * deployment that terminates TLS. */
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
  /** Enable Ed25519 signing on every sync message. Adds Byzantine defence:
   * a compromised client cannot push unsigned writes through the relay.
   * Requires a keyring with the local peer's signing identity and the
   * public keys of peers whose ops should be accepted. The server can
   * still read and mutate document contents because the payload is
   * signed, not encrypted. */
  sign?: boolean;
  /** Keyring for the signing layer. Required when `sign` is true. */
  keyring?: MeshKeyring;
  /** Network-adapter factory. Defaults to constructing a real
   * `WebSocketClientAdapter` against `url`. Injecting a factory lets tests (or
   * instrumentation) substitute a fake adapter so they stay off the network —
   * the production path leaves this unset. */
  adapterFactory?: (url: string, retryInterval?: number) => WebSocketClientAdapter;
  /** Called once per failed socket connection or transport error, on every
   * host. The client keeps retrying either way — this is a report, not a
   * recovery hook. With no callback the error is logged with
   * `console.warn`. See {@link containSocketErrors} for why the default is
   * not "let it throw". */
  onSocketError?: (error: Error) => void;
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
  /** True if the client was constructed with `sign: true`. Used by
   * $peerState primitives to validate per-primitive sign options. */
  signEnabled: boolean;
  /** Disconnect from the relay and tear down the Repo. Awaiting the
   * returned promise drains the Repo's subsystems cleanly. */
  close: () => Promise<void>;
}

/** Recover an Error from whichever error-event shape arrived. Node and Bun
 *  put the underlying error on `.error`; the browser event carries nothing,
 *  by design — the page console shows the failure and scripts cannot read
 *  it. */
function toSocketError(event: unknown, url: string): Error {
  if (typeof event === "object" && event !== null && "error" in event) {
    const carried = event.error;
    if (carried instanceof Error) return carried;
    if (carried !== undefined && carried !== null) return new Error(String(carried));
  }
  return new Error(`WebSocket connection to ${url} failed`);
}

/**
 * Stop a socket error from escaping the adapter as an uncaught exception,
 * and report it through `report` instead.
 *
 * `WebSocketClientAdapter.onError` ends with
 * `if (event.error.code !== "ECONNREFUSED") throw event.error`. That guard
 * assumes a Node `ws` error, which carries `code`. Bun's WebSocket error
 * event does not, so under Bun *every* failed connect attempt throws out of
 * the listener — once per `retryInterval`, for as long as the relay is
 * unreachable. Nothing catches it: the listener runs from the event loop, so
 * the throw lands as an uncaught exception and, under `bun test`, is charged
 * to whichever test happens to be running.
 *
 * In a browser the other branch runs and nothing throws, so this only bites
 * a client hosted on Bun or Node. The retry loop is untouched — the
 * reconnect timer is independent of this handler — so containing the throw
 * costs no reconnection behaviour.
 *
 * The original handler still runs first, keeping its debug logging and its
 * ECONNREFUSED discrimination. Adapters with no `onError` (test fakes) are
 * left alone.
 */
function containSocketErrors(
  adapter: WebSocketClientAdapter,
  url: string,
  report: (error: Error) => void
): void {
  const original = adapter.onError;
  if (typeof original !== "function") return;
  adapter.onError = (event) => {
    try {
      original(event);
    } catch {
      // The rethrow above is the whole reason this wrapper exists. The error
      // it carries is the same one `toSocketError` recovers below, so there
      // is nothing extra to keep here.
    }
    report(toSocketError(event, url));
  };
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
  if (options.sign && !options.keyring) {
    throw new Error(
      "Polly createPeerStateClient: { sign: true } requires a keyring. Pass { keyring: { identity, knownPeers, documentKeys: new Map(), revokedPeers: new Set() } } to enable signing."
    );
  }

  const adapter = options.adapterFactory
    ? options.adapterFactory(options.url, options.retryInterval)
    : new WebSocketClientAdapter(options.url, options.retryInterval);
  const connectionState = signal<PeerRelayConnectionState>("connecting");

  // Must run before the Repo constructor: `connect()` reads `adapter.onError`
  // when it registers the socket listener, so a later swap would not be seen.
  containSocketErrors(adapter, options.url, (error) => {
    connectionState.value = "disconnected";
    if (options.onSocketError) {
      options.onSocketError(error);
      return;
    }
    console.warn(`[polly] peer relay socket error (${options.url}):`, error.message);
  });

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

  // When signing is enabled, wrap the WebSocket adapter with a sign-only
  // MeshNetworkAdapter. This signs every outgoing message but does NOT
  // encrypt, so the relay server can still parse Automerge sync messages
  // and participate as a full peer (cron, HTTP handlers, etc.).
  const keyring = options.keyring;
  const networkAdapter: NetworkAdapterInterface =
    options.sign && keyring
      ? new MeshNetworkAdapter({
          base: adapter,
          keyringSource: () => keyring,
          encryptionEnabled: false,
        })
      : adapter;

  const repo = new Repo({
    network: [networkAdapter],
    ...(options.storage !== undefined && { storage: options.storage }),
  });

  return {
    repo,
    connectionState,
    adapter,
    signEnabled: options.sign === true,
    close: async () => {
      await repo.shutdown();
    },
  };
}
