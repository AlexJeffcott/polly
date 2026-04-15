/**
 * Access — declarative read/write authorisation for Polly's peer-first primitives.
 *
 * The new $peerState and $meshState primitives ship with a declarative `access`
 * option that compiles to server share policies ($peerState), signed-op access sets
 * ($meshState), or both when $peerState opts in via `sign: true`. Application code
 * expresses "who can read" and "who can write" as a pair of predicates over an
 * authenticated peer identity, and Polly enforces the predicates uniformly at every
 * transport and storage boundary.
 *
 * This module defines the types and a small set of primitive factories and
 * compositors. Primitive constructors in Phase 1 and Phase 2 will consume the
 * {@link Access} shape; the per-primitive "what does this compile to" resolution
 * lives in those constructors rather than here, because the target varies by
 * transport.
 *
 * @example
 * ```ts
 * import { $peerState } from "@fairfox/polly";
 * import { ownerAccess } from "@/shared/lib/access";
 *
 * const notes = $peerState("notes", defaults, {
 *   access: ownerAccess("peer-abc123"),
 * });
 * ```
 */

/**
 * An authenticated peer's identity as seen by Polly's authorisation layer.
 *
 * The shape is intentionally minimal: a stable {@link peerId} plus an optional
 * metadata bag that the transport's authentication hook can populate with
 * whatever it knows about the peer (session user id, device type, group
 * memberships, signing public key, etc.). Applications that need stronger
 * typing can parameterise {@link Access} on a narrower identity type.
 */
export interface PeerIdentity {
  /** Stable identifier for this peer. Must be unique within the application. */
  peerId: string;
  /**
   * Transport-specific metadata attached by the authentication layer. For
   * $peerState this is usually session data from the Elysia auth hook; for
   * $meshState this is usually the peer's verified signing public key and any
   * group memberships derived from it.
   */
  metadata?: Record<string, unknown>;
}

/**
 * A predicate over peer identities. Returns true if the identity satisfies the
 * access condition, false otherwise. Predicates must be pure — the same input
 * produces the same output — so that Polly can cache authorisation decisions
 * and reason about them in TLA+.
 */
export type AccessPredicate<Identity = PeerIdentity> = (identity: Identity) => boolean;

/**
 * Declarative read/write access for a single logical document. Every Polly
 * peer-first primitive that accepts an `access` option expects this shape.
 *
 * Read and write are independent: a predicate that returns true for read does
 * not imply anything about write. Applications that want "if you can write,
 * you can read" express it explicitly, either by reusing the same predicate
 * or by composing `read: or(readPred, writePred)`.
 */
export interface Access<Identity = PeerIdentity> {
  read: AccessPredicate<Identity>;
  write: AccessPredicate<Identity>;
}

// ─── Primitive predicate factories ──────────────────────────────────────────

/**
 * A predicate that accepts every identity. Useful for public documents and
 * for the "read" half of write-gated-but-publicly-visible patterns.
 */
export function anyone<Identity = PeerIdentity>(): AccessPredicate<Identity> {
  return () => true;
}

/**
 * A predicate that rejects every identity. Useful as an explicit "no-one can
 * write to this" marker and as the identity element for `or`.
 */
export function nobody<Identity = PeerIdentity>(): AccessPredicate<Identity> {
  return () => false;
}

/**
 * A predicate that accepts exactly one peer by id.
 */
export function onlyPeer<Identity extends PeerIdentity = PeerIdentity>(
  peerId: string
): AccessPredicate<Identity> {
  return (identity) => identity.peerId === peerId;
}

/**
 * A predicate that accepts any peer whose id is in the given set. The set is
 * captured at factory time and not re-read, so mutating the input array after
 * calling this has no effect on the returned predicate.
 */
export function anyOfPeers<Identity extends PeerIdentity = PeerIdentity>(
  peerIds: readonly string[]
): AccessPredicate<Identity> {
  const set = new Set(peerIds);
  return (identity) => set.has(identity.peerId);
}

// ─── Compositors ────────────────────────────────────────────────────────────

/**
 * Logical AND of two predicates. Accepts an identity only if both inputs
 * accept it. Short-circuits on the first false.
 */
export function and<Identity>(
  a: AccessPredicate<Identity>,
  b: AccessPredicate<Identity>
): AccessPredicate<Identity> {
  return (identity) => a(identity) && b(identity);
}

/**
 * Logical OR of two predicates. Accepts an identity if either input accepts
 * it. Short-circuits on the first true.
 */
export function or<Identity>(
  a: AccessPredicate<Identity>,
  b: AccessPredicate<Identity>
): AccessPredicate<Identity> {
  return (identity) => a(identity) || b(identity);
}

/**
 * Logical NOT of a predicate.
 */
export function not<Identity>(a: AccessPredicate<Identity>): AccessPredicate<Identity> {
  return (identity) => !a(identity);
}

// ─── Access constructors ────────────────────────────────────────────────────

/**
 * Public read and write for every peer. The default for documents that are
 * genuinely shared across everyone in the deployment. Not a sensible default
 * for $meshState, where the signing layer expects a bounded access set.
 */
export function publicAccess<Identity extends PeerIdentity = PeerIdentity>(): Access<Identity> {
  return {
    read: anyone<Identity>(),
    write: anyone<Identity>(),
  };
}

/**
 * Read and write restricted to a single owner peer. The strictest common
 * shape: a personal-notes document, a single-user setting store, anything
 * scoped to one device chain.
 */
export function ownerAccess<Identity extends PeerIdentity = PeerIdentity>(
  peerId: string
): Access<Identity> {
  const pred = onlyPeer<Identity>(peerId);
  return { read: pred, write: pred };
}

/**
 * Read and write restricted to a bounded group of peers. Both halves use the
 * same predicate, which is usually what groups want; applications that need
 * "some can read, fewer can write" should construct {@link Access} directly.
 */
export function groupAccess<Identity extends PeerIdentity = PeerIdentity>(
  peerIds: readonly string[]
): Access<Identity> {
  const pred = anyOfPeers<Identity>(peerIds);
  return { read: pred, write: pred };
}

/**
 * Everyone can read; only the supplied predicate can write. Common for
 * broadcast-style documents where one peer (or a group) publishes and the
 * rest observe.
 */
export function readOnlyExcept<Identity extends PeerIdentity = PeerIdentity>(
  writer: AccessPredicate<Identity>
): Access<Identity> {
  return {
    read: anyone<Identity>(),
    write: writer,
  };
}
