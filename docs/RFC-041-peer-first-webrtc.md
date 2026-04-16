# RFC-041 (sibling) — A peer-first capability for Polly: `$meshState`

Tracking issue: [AlexJeffcott/polly#41](https://github.com/AlexJeffcott/polly/issues/41)

Status: draft design for `$meshState`, the peer-replicated primitive for applications that must function with no server on the data path. A sibling primitive, `$peerState`, is designed in [RFC-041-peer-first.md](./RFC-041-peer-first.md); both ship together. The decision tree for choosing among `$sharedState`, `$peerState`, and `$meshState` is in [RFC-041-choosing.md](./RFC-041-choosing.md).

## The question worth answering

TLA+ is not easy. It is an unfamiliar specification language, an unfamiliar model checker, and a style of thinking about systems that frontend and fullstack TypeScript developers rarely encounter. Polly nevertheless made it easy for its users by putting the hard parts inside the framework and exposing a verified abstraction — developers write ordinary signal-based code and inherit TLA+'s guarantees without writing a single line of TLA+. The framework carries the burden; the user reaps the benefit.

Distributed systems are in the same category. CRDTs, causal delivery, signed operations, partition tolerance, Byzantine faults — none of this belongs in application code. Polly's opportunity with the two new peer-first primitives is to do for distributed systems what it already did for formal verification.

This document designs `$meshState`, the strongest resilience tier in the ordering. Its sibling `$peerState` answers the same framing for the middle tier — applications where the server stays on the data path so that cron and HTTP handlers can operate on document contents — and the choice between them is a resilience-requirements decision documented in [RFC-041-choosing.md](./RFC-041-choosing.md).

## What `$meshState` is for

`$meshState` is the primitive for data whose resilience story is *every device is a backup AND the application must function if the server is permanently gone*. Every client holds a full Automerge replica. Clients find each other through a small stateless signalling endpoint and open direct WebRTC data channels; document operations flow peer-to-peer between clients and never touch the server. The Polly Elysia app, if deployed at all, runs only a `signalingServer` plugin whose job is to relay SDP and ICE messages during connection setup and then get out of the way. No server-side replica of `$meshState` data exists; no server-side code can read or mutate it.

That last constraint is the reason to pick `$meshState` over its weaker sibling `$peerState`. Some applications need to survive the infrastructure. A family archive, a personal journal, a self-hosted collaborative tool, a prototype that needs to demonstrate it will continue working after the startup goes away — each of these has a resilience story where a dead server cannot mean dead data. `$meshState` satisfies that story by construction. The application layer does not need to implement export-and-restore flows, does not need to run a backup cron, does not need to coordinate client-side snapshots; it just uses the primitive, and the primitive does not depend on any central process for the data plane.

Signing and encryption are mandatory in `$meshState`, not options. The trust model requires them. Every operation is Ed25519-signed by its originating peer's device key and verified on receipt by every other peer. Document contents are encrypted with per-document symmetric keys provisioned to authorised peers at pairing time and never held by any server. Encryption operates at two layers: DTLS between peers over WebRTC (in-flight, free from the WebRTC stack, protects against TURN relays and any future message-relay fallback), and application-layer per-document symmetric keys applied to op payloads before they enter the transport (at-rest on every peer's IndexedDB or OPFS, plus defence in depth against any server that might see the transport payload). DTLS alone would leave a stolen device's local store readable; the application layer closes that gap.

Cron jobs that need to operate on `$meshState` data run on a *dedicated always-on peer*. This is a separate Node process that runs the same Polly client code, with its own device keypair provisioned with the same access as any other member of the group, deployable anywhere — Railway, a VPS, a Pi, a Tailnet-connected box, a laptop. It participates in the mesh as an ordinary client and happens never to sleep. It is opt-in. Applications that do not need server-side cron do not deploy one. Applications that do deploy one treat it as any other peer, and losing it is a degraded-cron situation, not a data loss situation.

## What Polly must hide

The primitive at the call site looks exactly like an existing Polly signal — the same shape as `$peerState`, because the surface is shared. Assigning to `.value` writes. Reading `.value` reads. Awaiting `.loaded` gates on hydration. Four specialised variants:

```typescript
const draft    = $meshText("draft", "")                  // concurrent text edits
const visits   = $meshCounter("visits", 0)               // commutative increments
const todos    = $meshList<Todo>("todos", [])            // ordered list with insert/remove
const settings = $meshState<Settings>("settings", {...}) // general JSON-shaped state
```

Each is a `Signal<T>` with the same interface as its `$peerState` counterpart. The CRDT library underneath is identical — Automerge-Repo — and the operation-capture logic for the specialised variants is shared code. Application code is indistinguishable between `$meshState` and `$peerState` except for the import name and the options type.

The declarative `access` API has extended semantics for `$meshState`:

```typescript
$meshState<Settings>("settings", defaults, {
  access: {
    read:  peers.owner,                    // resolves to a set of device public keys
    write: peers.owner,
  },
  schemaVersion: 3,
  migrations: { /* ... */ },
})

$meshText("family-notes", "", {
  access: {
    read:  peers.anyIn("family"),          // group membership
    write: peers.anyIn("family"),
  },
})
```

The framework translates each `access` declaration into two things underneath: a public-key set for signature verification, and a per-document symmetric encryption key. Both are provisioned at pairing time, both rotate on signed access-set updates, and both live in client-side storage that the application never touches directly. The application code says "this document is readable by the `family` group"; Polly resolves the group to public keys, applies the encryption, verifies the signatures, and enforces the access check on every incoming operation. The application never writes crypto code, never sees a key, never implements a share policy, and never verifies a signature.

## Why `$meshState` is its own primitive

The two new primitives serve two distinct resilience tiers. `$peerState` keeps the server on the data path so that cron and HTTP handlers can operate on document contents; the cost is that the server must be trusted and running. `$meshState` removes the server from the data path entirely; the cost is that server-side compute on the data is not possible, and dedicated cron peers have to be run separately if scheduled work is needed.

Four properties follow from `$meshState`'s trust model, and each is a property `$peerState` cannot offer.

**No server on the data path.** `$peerState`'s relay is a full replica, but it is the only replica every client talks to, and when it is unreachable, no client reaches any other client. `$meshState` never has a replica on the server, so the server's reachability is irrelevant to the data plane — two clients that can reach each other will sync, regardless of what the signalling endpoint is doing.

**Byzantine tolerance by construction.** Every operation is signed; every replica verifies before applying. A compromised device can be revoked through a signed access-set update, after which its operations are rejected by all honest peers. A compromised server (the signalling endpoint) is powerless, because it has no signing key of its own and no ability to forge ops.

**End-to-end encryption by construction.** Document contents are encrypted before they leave the originating peer. No server, including the signalling endpoint and any TURN relay, ever holds plaintext. The server-facing Polly bundle does not contain the primitive at all — `$meshState` has no server-side implementation — so a server-side `import` of `$meshState` is a build error rather than a runtime surprise.

**Location independence.** `$peerState` needs a publicly-addressable TLS relay to host its `Repo`. `$meshState`'s signalling peer is stateless and can run anywhere — Railway, a Cloudflare Worker, a Pi, a Tailnet, a laptop — because it holds no data. Moving the signalling peer is a configuration change, not a migration. The data plane has no hosting dependency once connections are established.

These are not abstract benefits. Each corresponds to a class of application whose resilience requirements cannot be met by keeping a replica on any server Polly runs. Shipping `$meshState` as its own primitive, with these properties baked into the contract, is what lets the application layer stay thin — the developer writes signal code and inherits the full resilience tier.

## The transport

Each device runs a Polly client with a `MeshNetworkAdapter` implementing the new `CrdtNetworkAdapter` interface. The adapter wraps Automerge-Repo's network adapter over `RTCDataChannel` and handles the signing, verification, and encryption pipeline around every incoming and outgoing op. Connection setup goes through a stateless signalling endpoint that exchanges SDP offers and ICE candidates and then gets out of the way; the data plane never touches the signalling server again.

A new `signalingServer` Elysia plugin exposes the signalling WebSocket route. Its responsibilities are authenticating upgrade requests, routing SDP and ICE messages between authenticated peers, and holding no state. The existing Polly plugin is untouched, and the sibling `peerRepo` plugin from the `$peerState` design lives alongside it on its own distinct route. A single Polly Elysia app can host all three — the existing `polly()` plugin for `$sharedState`, `peerRepo()` for `$peerState`, and `signalingServer()` for `$meshState` — on different WebSocket routes, sharing the same auth hook.

NAT traversal uses STUN for public-IP discovery and TURN as a fallback for peers behind symmetric NATs. TURN relays the DTLS payload of the data channel, which is already encrypted by the WebRTC stack; inside that payload, Polly has also applied application-layer encryption, so a TURN relay sees only doubly-encrypted bytes. A coturn instance on a small VPS handles TURN in practice.

An optional always-on peer participates in the mesh as an ordinary client. It holds replicas of documents whose encryption keys it has been provisioned with and runs cron jobs against those documents by opening Polly signals and mutating them. It does not hold keys for documents the application has declared private from it, and therefore cannot decrypt them. The cron peer is not on the critical path for client-to-client sync; if it is offline, scheduled jobs pause, but peers continue to reach each other directly.

## Resilience

**Client offline, other peers reachable.** Writes happen against the local replica. On reconnect, the adapter negotiates direct channels to whichever peers are online and syncs. No central bottleneck, so reconnection is as fast as the slowest available peer.

**Client online, all other peers offline.** The local replica accepts writes. Sync waits for peers to return. This is the limit case for any peer-first system, and Polly's guarantee is that the writes are durable locally and will propagate on reconnect.

**Total data loss on one peer.** The affected peer reconnects with an empty replica. The sync protocol pulls the current state from any other peer that holds it. Recovery is symmetrical for every peer in the mesh — there is no "the server went down" case, because there is no server on the data path. Recovery is guaranteed provided any peer still holds the history.

**Signalling server gone permanently.** Existing peer-to-peer connections are unaffected and continue to sync. New connections — new peers joining, or existing peers returning after a disconnect — are blocked until signalling is restored somewhere. This is the price of needing peer discovery at all. It is not a data-loss situation, and it is trivially recoverable by pointing clients at a new signalling endpoint.

**Partition.** Two groups of peers cannot reach each other. Each group makes progress locally. On heal, the sync protocol converges. The always-on cron peer in one partition continues to run against the data it can see; when the partition heals, its ops merge with the other group's writes through the CRDT's guarantees.

**Byzantine peer.** A peer whose private key is compromised can sign malicious writes. Other peers receive the writes, verify the signature against the access set, and apply them. Revoking the compromised key is a write to the document's access set, which is itself a signed CRDT operation. Once revocation has propagated, the compromised key can no longer produce accepted writes, and the application can audit the signed history to identify what the compromised peer did. This is a limited Byzantine defence — it does not cover key theft that also compromises the revocation path — but it is a real defence that `$peerState` without `sign: true` does not provide.

**Schema skew.** Handled identically to `$peerState`. Every op carries its schema version; versioned ops are rejected at sync time if they predate the document's current version. The migration protocol is shared between the two primitives.

**History growth.** Compaction is analogous to the `$peerState` case. The verified invariant is that a peer may only drop ops whose presence on a configurable quorum of other peers is confirmed. "Quorum" replaces the server's role as the single confirmation point; applications can trade durability against storage by picking a majority or a k-of-n threshold.

## TLA+ verification

The TLA+ specification for `$meshState` is a superset of the specification for `$peerState`. It covers every convergence, recovery, and migration property of the sibling primitive and adds three more. This is why shipping both primitives in one release is cheaper than shipping either alone across two milestones — the hard verification work happens once, and `$peerState` is the subset that does not require encryption or revocation (it offers optional `sign: true`, which reuses the same verified signing code paths).

The spec models N peers, each with a keypair and a local replica, a signalling layer that routes connection setup without observing data, pairwise data channels between peers, an access set per document containing public keys, signed operations, and the shared migration protocol. Properties to verify:

- **Strong eventual convergence.** Inherited from Automerge, restated in the TLA+ model.
- **Signature soundness.** A peer whose public key is not in the access set cannot produce an operation that any honest peer will apply.
- **Revocation convergence.** After a revocation is issued and propagated, no operation signed by the revoked key is ever applied again, even if the revoked peer continues to broadcast.
- **Privacy soundness.** A peer not in the read set cannot observe plaintext document contents, regardless of what it sees on the signalling layer or the TURN relay.
- **Recovery convergence.** After any single peer's total data loss, recovery converges provided at least one other peer retains history.
- **Migration convergence.** Identical to the `$peerState` specification.
- **Compaction safety.** A peer may only drop ops whose presence on a configurable quorum of other peers is confirmed.

These seven properties describe what a developer who writes `$meshState("…")` is entitled to expect from the primitive. Each corresponds to a real failure mode if Polly gets the protocol wrong, and each is the kind of guarantee the framework exists to carry.

## The hard parts

Three things are genuinely harder in `$meshState` than in `$peerState`. Naming them makes the trade-off legible.

**WebRTC is operationally fiddly.** Connection establishment has more moving parts than a WebSocket, failure modes are varied, and browser debugging is weaker. Polly's answer is that the fiddliness lives inside the adapter and inside Polly's own tests, not inside the application. The developer writes signals; the adapter reports a connection-state signal that Polly exposes as `$meshConnectionState`, which the application can render as a diagnostic UI or ignore entirely.

**Key management has a UX surface.** Pairing, rotation, and revocation all need an out-of-band channel for the first key exchange, and all need a mental model the user can follow. Polly's answer is that the key-management API is declarative in the same way the access API is declarative: the application says "this document is readable by the `family` group," and Polly handles pairing, key provisioning on new devices, and revocation-on-loss through a small set of signal-shaped primitives. The framework ships with a reference pairing UI that applications can embed or replace.

**TURN costs money and needs operation.** A coturn instance needs a small VPS, monitoring, and someone to notice when it fails. This is a real cost, and it is not one `$peerState` incurs for its own relay. The counter-weight is that the TURN instance is strictly smaller and strictly more replaceable than the relay `$peerState` already requires, so the combined operational footprint of shipping both primitives together is a modest addition rather than a doubling.

None of these is a reason to avoid the primitive. They are reasons the primitive's implementation is more work than `$peerState`'s, which is exactly the kind of work Polly exists to do once so that every application using the framework gets the benefit for free.

## First milestone

The primitive surface shares its shape with `$peerState` — same signal ergonomics, same specialised variants, same declarative `access` API. What is specific to `$meshState`:

1. `$meshState`, `$meshText`, `$meshCounter`, `$meshList` primitives, implemented on the shared base machinery with signing and encryption hard-coded on.
2. `MeshNetworkAdapter` implementing `CrdtNetworkAdapter`, wrapping Automerge-Repo's network adapter interface over `RTCDataChannel`.
3. `signalingServer` Elysia plugin exposing a stateless WebSocket route for SDP and ICE exchange.
4. Optional always-on cron peer container with Polly plus a small cron runner, deployable anywhere, provisioned only with the keys for documents it is authorised to read.
5. Signing and verification for every op, backed by the shared crypto machinery that `$peerState`'s `sign: true` option also uses.
6. End-to-end document encryption with per-document symmetric keys. `$peerState` does not offer encryption (it would prevent the server from parsing sync messages); encryption is exclusive to `$meshState`.
7. Pairing, rotation, and revocation flows exposed as Polly primitives with a reference UI.
8. TLA+ specification covering the seven properties above, with TLC model-checking configuration.

This milestone is coordinated with the `$peerState` milestone in [RFC-041-peer-first.md](./RFC-041-peer-first.md). The shared work — primitive layer, CRDT layer, declarative `access` API, schema-version protocol, migration helper, crypto machinery, and the enforcement of the mixing rules in [RFC-041-choosing.md](./RFC-041-choosing.md) — is done once and serves both primitives.

Out of scope for this primitive: tab-to-tab `BroadcastChannel` sync, migration of existing `$sharedState` consumers, and any actual blob storage or large-file sync (see the follow-up RFC).

## Open questions

1. **Bandwidth efficiency in a full mesh.** N peers exchanging ops pairwise is N² connections. For small peer counts this is fine; for larger counts the mesh wants gossip or tree-based propagation. At what peer count does the naive full mesh stop being the right default, and does Polly expose the topology choice to the application?
2. **Signalling-peer discoverability.** Clients need to find the signalling endpoint on startup. A hardcoded URL works but is inflexible. Does Polly ship a discovery mechanism, or is the endpoint a configuration value the application provides?
3. **Pairing without an always-on peer.** First-device setup has no peers to pair with. The pairing flow needs to bootstrap from scratch — a QR code, a shared secret, a cloud-hosted introducer — and the choice affects both the UX and the security model. Which does Polly ship as the default?
4. **Signed-op overhead.** Every op carries a signature, which adds bytes per op and CPU per verification. At what op rate does this start to matter, and is there a batching strategy that preserves the verification property?
5. **Concurrent access-set edits.** Two peers simultaneously revoke different keys. The CRDT merges the revocations correctly, but what about the window during which one peer has applied its revocation and the other has not? Does the TLA+ spec need a liveness bound on revocation propagation, and what is a reasonable value?
6. **Cron peer key scope.** A single always-on cron peer may be authorised to read some `$meshState` documents and not others, determined by which keys it has been provisioned with. Does Polly ship a declarative way to express "this cron job operates on these documents," and how does that interact with rotation?
