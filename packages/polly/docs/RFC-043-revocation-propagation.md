# RFC-043 — Revocation propagation in the Polly mesh

Tracking issue: TBD

Status: draft. The mesh today ships the *primitives* of peer revocation — signed revocation records, an authority model, the keyring mutation that engages the adapter-level drop — but no automatic mechanism to put a revocation on the wire and ensure every peer applies it. This RFC designs that mechanism.

## The question worth answering

A device gets lost, stolen, or sold. The user opens the agenda app on their main device and chooses "revoke this paired device." What should happen?

Polly today gives a clean answer for one piece of that question: the user's main device adds the revoked peerId to its keyring's `revokedPeers` set, and `MeshNetworkAdapter` drops every subsequent direct message from that peer. The signed-revocation primitives in `src/shared/lib/revocation.ts` produce a transportable binary record. What does not yet exist is the protocol layer that takes a revocation record from one peer and lands it in the keyring of every other peer in the mesh, plus on the disk-backed keyring of any peer that was offline at issue-time.

The end-to-end test `scripts/e2e-mesh-revocation-runtime.ts` made this gap visible. In a two-peer geometry the adapter-level drop is sufficient: peer A revokes peer B, and B has no other route to A's document state. In a three-peer geometry it is not. Peer B's writes still reach peer A through peer C's gossip, because C has not learned that B is revoked. Revocation as a transport-level operation cannot cross the gossip mesh; revocation as a protocol-level fact has to.

This RFC chooses the *protocol-level* model. Every peer learns of every revocation; every peer's adapter drops the revoked peer's messages from that moment forward. The model is forward-only — ops authored by a revoked peer before the revocation propagated continue to live in the document, because Automerge histories are monotonic and unmerging is its own design conversation (see *non-goals* below). Forward-only is the same model identity revocation uses in practice: the kick takes effect going forward; past contributions are not unsaid.

## Goals

1. A revocation issued by an authorised peer reaches every other peer in the mesh, including peers that were offline at issue-time.
2. The receive path is automatic. Applications do not subscribe to a "revocation event"; they call `client.revokePeer(peerId, reason?)` on one device and observe consistent behaviour across every other device without further code.
3. Revocations persist. A peer that applies a revocation and then restarts continues to enforce it.
4. The adapter-level drop remains the enforcement mechanism. The protocol layer's only job is to ensure every peer's keyring carries the revocation.
5. The revoked peer can discover that it has been revoked, surfacing a recoverable UX rather than silently disappearing.
6. Wire-format additions are versioned. Polly's mesh protocol is small enough that adding a control-message type matters; the design must allow future expansion without breaking 0.70 peers.

## Non-goals

This RFC does not design retroactive revocation. Ops authored by a revoked peer before propagation stay in the document. The literal request "remove every contribution from peer B from every peer's view" requires either filtering Automerge ops by their authoring actor at apply-time (invasive into polly's sync handling and Automerge's internal model) or forking the document to a new id that omits B's history (a UX hammer that breaks every other peer's local state and breaks `$meshState` key stability). Both are real options for a future RFC; neither is in scope here.

This RFC does not design revocation of the issuer's own authority. A peer that revokes another peer remains authorised; nothing in this design prevents the revoked peer from issuing a counter-revocation if it is still able to sign one. The authority model in section *Authority* below decides who *can* issue a revocation that other peers accept; an attacker with full control of a peer's signing key can do anything that peer could do, and recovery from that state is part of the threat model for the pairing flow, not for revocation.

This RFC does not design the user-facing UI for revocation. Fairfox and lingua own that surface; polly exposes a `revokePeer` API and a diagnostic stream.

## The protocol

A revocation is broadcast through a new mesh control-message type that travels alongside Automerge sync messages on the same WebRTC data channels. The control-message type is independent of any document — it carries no `documentId` — and is processed by the mesh client before any sync subsystem sees it.

### Wire format

The transport envelope already exists: `signEnvelope` plus `encodeSignedEnvelope` produce a signed binary blob whose `senderId` carries the issuer's peer id. The revocation-payload format is the existing `RevocationRecord` serialised by `serialiseRevocationPayload` (magic `PRV1`, version 1). What changes is the outer message envelope, which today is a wrapped Automerge `Message`.

A control-message envelope adds one byte at the front of the encrypted payload to discriminate the inner contents:

```
[outer signed envelope: as today]
  └── plaintext payload:
        [1 byte: type tag]
          0x00 → Automerge sync message (current behaviour)
          0x01 → revocation record (PRV1)
          0x02 → revocation-set summary (see Reconnect re-broadcast)
        [N bytes: type-specific body]
```

The type tag goes inside the encrypted payload, not the signed-envelope header, so the type itself is confidential and authenticated. Receivers that see an unknown type tag emit a `drop:unknown-control-type` diagnostic (added to the existing `mesh-diagnostics` stream) and drop the message. This is the wire-format extension point; future RFCs add new types without re-versioning the envelope.

Polly 0.70 peers do not understand the type byte. Mixing a 0.70 peer with a 0.71-or-later peer on the same mesh therefore breaks: the 0.70 peer interprets the type byte as part of the Automerge sync message and produces garbage. The breaking change requires a polly minor or major bump and a coordinated rollout. The alternative — sending revocations through a separate WebRTC data channel, leaving the existing channel exactly as today — preserves backward compatibility but doubles the mesh's transport complexity and creates an ordering problem (was the revocation seen before or after the sync message it ought to gate?). The single-channel approach is the simpler design and the right trade-off.

### Issuing a revocation

`client.revokePeer(peerId, reason?)` does the following, atomically with respect to the local keyring:

1. Build a `RevocationRecord` via `createRevocation`, using the local peer's signing keypair and peerId as issuer.
2. Encode it via `encodeRevocation`.
3. Apply it to the local keyring via `applyRevocation` so the issuing peer's adapter starts dropping the revoked peer immediately.
4. Persist the record in keyring storage (see *Persistence* below).
5. Broadcast the encoded record to every currently-connected peer, wrapped in a control-message envelope with type tag `0x01`.

The function returns once steps 1-4 complete. Step 5 is fire-and-forget at the broadcast point; reliability is delivered by the reconnect re-broadcast in section *Reconnect re-broadcast*.

### Receiving a revocation

The mesh client's incoming-message handler peels the type tag off every decrypted control-message payload before forwarding to the Automerge sync layer. On type `0x01`:

1. Decode and verify via `decodeRevocation`. Verification covers issuer membership in `knownPeers`, optional `revocationAuthority` membership, and signature validity (the existing path in `revocation.ts`).
2. If verification fails, emit `drop:revocation-rejected` with the specific `RevocationError.code` and stop.
3. If the revocation names the receiving peer itself as the revoked target, the receiver does not silently apply it to its own keyring. Instead the receiver emits `revoke:self-targeted` to the diagnostic stream, leaves the keyring untouched, and surfaces a `selfRevocation` field on the `MeshClient` state so the application can render a "you have been revoked" UX. The receiver continues to accept the revocation when re-broadcasting (see *Reconnect re-broadcast*); the only special case is the local enforcement, which would silence the revoked peer from notifying its user.
4. If the revocation is already present (a peer can receive the same revocation from multiple sources), it is dropped silently and a `revoke:duplicate` diagnostic is emitted with a counter incremented in the existing peer-state snapshot.
5. Otherwise, apply via `applyRevocation`, persist, and emit `revoke:applied`.

The order matters. Verification before any keyring mutation; self-targeted check before applying to the local keyring; persistence before emitting the diagnostic so a crash between mutation and persist does not lose state on the next start.

### Persistence

Revocations live in keyring storage alongside the existing keyring fields. The persisted format is a list of encoded revocation blobs, not a deserialised set, so re-application from disk goes through the same verification path as fresh receipt. This is intentional: it means a revocation that was valid at receipt time but is no longer verifiable (e.g., the issuer's public key has since been removed from `knownPeers`) is dropped on the next load with a clear diagnostic, rather than silently surviving as an unverified entry.

`keyring-storage.ts` gains a `revocations` field in the persisted shape and a load-time helper that re-applies each. Existing keyrings without the field load with an empty revocation list; the migration is forward-only.

### Reconnect re-broadcast

The hardest piece. A peer that was offline at the moment of revocation must still learn about it. The reliable-broadcast property cannot be guaranteed by the issuer alone — the issuer may have been offline when the offline peer reconnected.

The design uses gossip plus a hash-based summary. On every newly-established WebRTC data channel (the `peer-candidate` event in the existing adapter), both ends exchange a *revocation-set summary*: a sorted list of `(revokedPeerId, issuedAt, issuer-signature-prefix)` tuples representing every revocation currently in the keyring. Wire-encoded with type tag `0x02`.

After exchange, each peer computes the set difference. For revocations the remote peer has and the local peer does not, the local peer requests the full encoded blobs (a follow-up control message of a third type tag, or a piggyback on the summary exchange — section *Open questions* below). For revocations the local peer has and the remote does not, the local peer pushes them. The result: every newly-connected peer is brought to the union of both peers' revocation sets within one round-trip.

This handles the "offline at issue-time" case naturally. A peer that was offline learns the revocation from any peer it reconnects to, transitively from any peer who learned from a peer who learned from the issuer. The propagation latency is bounded by the longest unbroken-online path between the offline peer and any peer that holds the revocation.

The summary itself is small: a revocation has a stable hash; the summary entry is on the order of 50 bytes. A keyring with a thousand revocations is 50 KB — cheap on a fresh data channel.

### Authority

Today's first-cut accepts any signed revocation from a peer in `knownPeers`. Production deployments need a stricter model. Two options.

**Option A — explicit authority set.** `keyring.revocationAuthority` is a non-empty set of peer ids allowed to issue revocations that the local peer applies. Already plumbed in `decodeRevocation`. This is the right shape for hierarchical setups: a workspace administrator's device is in every member's authority set; member devices can revoke nothing.

**Option B — symmetric self-authority for paired identities.** For fairfox-shaped apps where every paired device is an equal member of one user's identity, any of the user's paired devices can revoke any other. The authority set is "every peer whose identity public key matches the local user's identity public key under some sharing scheme."

This RFC chooses option B as the default for `$meshState` and option A as the configuration override. The default behaviour matches the user's mental model: "all my devices are me; any of them can kick any other." The override exists for the workspace shape and is wired through `revocationAuthority` exactly as today.

Implementation: when `revocationAuthority` is `undefined`, the receiver accepts any revocation whose issuer shares the local peer's user identity (a new field on the keyring, populated at pairing time). When `revocationAuthority` is set, the existing behaviour stands.

### Discoverability

A revoked peer learns of its revocation through the normal receive path. The `revoke:self-targeted` diagnostic fires; the application binds to it through the existing diagnostic stream and shows a "you have been revoked by your other device on date X" screen. The peer's mesh client stops sending writes (the local enforcement: refuse to author ops when `selfRevocation` is non-null) but stays connected long enough to receive any further revocations targeting it.

This is what option B's symmetric model needs: the revoked peer can tell which sibling device kicked it and surface a message, rather than silently appearing to be offline.

### Diagnostic stream additions

Four new event kinds extend the existing `mesh-diagnostics` enumeration:

- `revoke:applied` (replaces today's placeholder) — when a remote revocation lands in the local keyring.
- `revoke:duplicate` — a revocation already known was received again.
- `revoke:rejected` — verification failed; carries the `RevocationError.code`.
- `revoke:self-targeted` — the local peer is the revocation's target.

Two existing kinds (`pair:invite-accepted`, `revoke:issued`) keep their shapes. The diagnostic stream is the test surface and the production observability surface; every change to the protocol is a change to the diagnostic vocabulary.

## Test plan

Three new e2e scripts cover the protocol surface:

1. `scripts/e2e-mesh-revocation-propagation.ts` — three peers; A revokes B; verifies that C drops B's subsequent direct messages and emits `revoke:applied` plus `drop:revoked-peer`; verifies that A, B, and C agree on the revocation set.
2. `scripts/e2e-mesh-revocation-offline-catchup.ts` — three peers (A, B, C); C goes offline; A revokes B; C comes online; verifies that C learns the revocation from A on the reconnect re-broadcast and that B's writes routed through any peer are dropped by C.
3. `scripts/e2e-mesh-revocation-self-detection.ts` — two peers; A revokes B; verifies that B receives `revoke:self-targeted`, B's `selfRevocation` field becomes non-null, B's outbound writes stop, and B's UI surface (in the e2e consumer) can read the revocation reason and timestamp.

Unit tests cover the wire-format additions: the type-tag dispatch, the summary exchange, the difference computation, the persistence round-trip, and the authority defaults.

## Open questions

**Q1.** Does the revocation-set summary include `issuedAt`? If two peers issue conflicting revocations (A revokes B, B revokes A) and a third peer C receives them out of order, the local keyring ends up with both peers in `revokedPeers`, and the mesh stalls. One resolution: any peer in `revocationAuthority` who has been revoked is no longer authoritative; the second revocation in causal-clock order wins. Requires a Lamport timestamp on the revocation record rather than wall-clock `issuedAt`.

**Q2.** How does the summary exchange handle disagreement on signature-prefix? Two peers might have different encodings of the same logical revocation if either side's `decodeRevocation` produced different prefix bytes. Suggested mitigation: hash the canonical `RevocationRecord` bytes, not the signed envelope, since the envelope carries a nonce and the record does not.

**Q3.** Is there a maximum revocation-set size? A long-lived mesh with high churn could accumulate thousands of revocations. At what point does the summary cost matter? Suggested mitigation: a `tombstone-expire` policy after N days, applied to revoked peers who have been offline for longer than N, on the assumption that a peer not connecting in N days is presumed permanently gone. Requires a per-peer last-seen timestamp.

**Q4.** What does `revokePeer` return? A bare promise that resolves once the local keyring update has persisted, or a richer object that lets the caller observe propagation across the mesh? The latter requires the issuer to track acknowledgements from every connected peer, which is more machinery for marginal value. Suggested default: bare promise; expose a `getRevocationPropagationSnapshot()` on `MeshClient` for applications that want to surface "this revocation has reached N of M paired devices."

**Q5.** Should the wire format include a TTL or expiry on the revocation itself? A revocation is a permanent statement in the current model; a temporary "soft block" is a different feature and might want a different envelope.

## Next steps

If this design holds, the implementation breaks into three PRs of decreasing dependence:

1. The wire-format type tag plus the type-tag dispatch in `MeshClient`'s incoming-message handler. No new behaviour, just a tagged channel that the next PR uses.
2. `client.revokePeer` issuing + the persistence path + the receive path + the three new diagnostic kinds. Single-connection scope; the gossip layer comes later. The two-peer e2e script proves this surface.
3. The revocation-set summary exchange on `peer-candidate`, plus the offline-catchup e2e. This is the piece that delivers the protocol's reliable-broadcast property.

Q1–Q5 are resolved during implementation review of PR 2; none of them block the wire-format work in PR 1.
