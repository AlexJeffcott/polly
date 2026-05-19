/**
 * mesh-diagnostics — typed event stream for observable mesh failures and
 * state transitions.
 *
 * The mesh network adapter's incoming path has seven branches that drop a
 * message and return undefined: a malformed signed envelope, a revoked
 * peer, an unknown peer, a bad signature, a malformed encrypted envelope,
 * a missing document key, and a bad decryption. Each branch is correct —
 * the adapter must not surface tampered or unidentifiable bytes to the
 * Repo — but the drop is invisible to anything observing the application.
 * The classic symptom is "the other peer typed something and nothing
 * arrived" with no error anywhere.
 *
 * This module exposes a typed emit-and-subscribe stream that the adapter
 * (and the pairing and revocation paths) write to. Tests subscribe to
 * assert that exactly the expected diagnostics fired and no others;
 * production code can attach an observability sink that turns the stream
 * into telemetry or a user-visible diagnostic surface.
 *
 * The stream is module-level. Listeners are deduplicated by reference;
 * subscribe returns an unsubscribe function. Listener exceptions are
 * caught and dropped so a buggy observer cannot tear the network path.
 */

/** All diagnostic event kinds, discriminated by the `kind` field. */
export type MeshDiagnostic =
  // Incoming-message silent drops in MeshNetworkAdapter.tryUnwrap.
  | { kind: "drop:malformed-signed-envelope"; reason?: string }
  | { kind: "drop:revoked-peer"; senderId: string }
  | { kind: "drop:unknown-peer"; senderId: string }
  | { kind: "drop:bad-signature"; senderId: string; reason?: string }
  | {
      kind: "drop:malformed-encrypted-envelope";
      senderId: string;
      reason?: string;
    }
  | {
      kind: "drop:missing-doc-key";
      senderId: string;
      documentId: string;
    }
  | {
      kind: "drop:bad-decryption";
      senderId: string;
      documentId: string;
      reason?: string;
    }
  // Pairing-flow transitions.
  | { kind: "pair:invite-issued"; peerId: string }
  | { kind: "pair:invite-accepted"; peerId: string; issuerId: string }
  // Revocation-flow transitions.
  | { kind: "revoke:issued"; revokedPeerId: string; issuerId: string }
  | { kind: "revoke:applied"; revokedPeerId: string };

/** A diagnostic event with the wall-clock timestamp the emitter stamped. */
export type MeshDiagnosticEvent = MeshDiagnostic & { timestamp: number };

/** Callback shape for subscribers. */
export type MeshDiagnosticListener = (event: MeshDiagnosticEvent) => void;

const listeners = new Set<MeshDiagnosticListener>();

/**
 * Emit a diagnostic to every active subscriber. Synchronous. Listener
 * exceptions are swallowed.
 */
export function emitMeshDiagnostic(diagnostic: MeshDiagnostic): void {
  const event: MeshDiagnosticEvent = { ...diagnostic, timestamp: Date.now() };
  for (const listener of listeners) {
    try {
      listener(event);
    } catch {
      // A buggy listener must not break the network path. The diagnostic
      // is intentionally a side-channel; if telemetry collapses, the mesh
      // keeps moving messages.
    }
  }
}

/**
 * Subscribe a listener. Returns an unsubscribe function. Idempotent on
 * the same listener reference — subscribing the same function twice
 * registers it once.
 */
export function subscribeToMeshDiagnostics(listener: MeshDiagnosticListener): () => void {
  listeners.add(listener);
  return () => {
    listeners.delete(listener);
  };
}

/**
 * Convenience for tests and trace recorders: subscribe, collect every
 * event into an array, return the array and a stop function that
 * unsubscribes. The returned array is the live capture buffer — reads
 * see new events the moment they fire.
 */
export function recordMeshDiagnostics(): {
  events: ReadonlyArray<MeshDiagnosticEvent>;
  stop: () => void;
} {
  const captured: MeshDiagnosticEvent[] = [];
  const stop = subscribeToMeshDiagnostics((event) => {
    captured.push(event);
  });
  return { events: captured, stop };
}

/**
 * Test-only: drop every subscriber. Use in `afterEach` to guarantee
 * isolation between tests when a stop function was missed. Not exported
 * from the mesh subpath in production builds — tests reach in directly.
 */
export function clearMeshDiagnosticListeners(): void {
  listeners.clear();
}
