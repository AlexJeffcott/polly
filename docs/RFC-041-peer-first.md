# RFC-041 — A peer-first capability for Polly: `$peerState`

Tracking issue: [AlexJeffcott/polly#41](https://github.com/AlexJeffcott/polly/issues/41)

Status: draft design for `$peerState`, the peer-replicated primitive where the server participates as a full peer on the data path. A sibling primitive, `$meshState`, is designed in [RFC-041-peer-first-webrtc.md](./RFC-041-peer-first-webrtc.md); both ship together. The decision tree for choosing among `$sharedState`, `$peerState`, and `$meshState` is in [RFC-041-choosing.md](./RFC-041-choosing.md).

## The question worth answering

TLA+ is not easy. It is an unfamiliar specification language, an unfamiliar model checker, and a style of thinking about systems that frontend and fullstack TypeScript developers rarely encounter. Polly nevertheless made it easy for its users by putting the hard parts inside the framework and exposing a verified abstraction — developers write ordinary signal-based code and inherit TLA+'s guarantees without writing a single line of TLA+. The framework carries the burden; the user reaps the benefit.

Distributed systems are in the same category. CRDTs, vector clocks, share policies, signed operations, schema skew across replicas, Byzantine peers, partition recovery — none of this is natural territory for a TS developer trying to ship an application. Polly's opportunity with the two new peer-first primitives is to do for distributed systems what it already did for formal verification: absorb the hard parts into the framework, ship the abstractions with strong guarantees, and let developers write signal code.

This document designs `$peerState`, the middle tier in the resilience ordering. Its sibling `$meshState` answers the same framing for the strongest resilience tier — applications that must function with no server dependency at all — and the choice between them is a resilience-requirements decision documented in [RFC-041-choosing.md](./RFC-041-choosing.md).

## What `$peerState` is for

`$peerState` is the primitive for data whose resilience story is *every device is a backup, the server included*. Every client holds a full Automerge replica. The Polly server also holds a full replica, participating in the sync protocol as an ordinary peer. If the server loses its storage volume, it rehydrates from the first clients to reconnect; if it is temporarily unreachable, clients continue writing locally and converge when it returns. The server is not the source of truth — the union of all replicas is — but it has a distinguished role in two senses: it is always on, and it is the only peer that the existing Polly Elysia app runs inside, so server-side code has direct access to document contents.

That direct access is the reason to pick `$peerState` over its stronger sibling `$meshState`. Cron jobs, HTTP handlers, scheduled jobs, aggregation, search indexing, summarisation, backup pipelines — anything that needs to read or mutate a document from server-side code — all work naturally because the server participates in the data plane. A nightly cron that rebalances chores, a search endpoint that scans across documents, a webhook handler that updates state on an external trigger, an AI summarisation job that reads a conversation and writes a summary: all of these are ordinary Polly code running inside the Elysia app, operating on document handles just as client code does.

The cost of server-side compute is that the server must be trusted to see document contents. For data where that trust is wrong — personal notes, drafts, anything whose threat model includes the Polly infrastructure itself — `$meshState` is the right choice. `$peerState` offers a `sign: true` option for applications that want per-operation signatures for audit and Byzantine defence without sacrificing server-side compute. Encryption is not offered on `$peerState` because it would prevent the server from parsing Automerge sync messages, degrading it from a full peer to a dumb byte relay — which is exactly what `$meshState` already is. Applications that want encrypted state should use `$meshState`. The default is plaintext and unsigned, matching the common-case collaborative-app workload.

## What Polly must hide

The primitive at the call site looks exactly like an existing Polly signal. Assigning to `.value` writes. Reading `.value` reads. Awaiting `.loaded` gates on hydration. There is no `change` block, no document handle, no CRDT object, no conflict callback, no clock visible to the user. Four specialised variants cover the shapes where naive value diffing gives wrong semantics:

```typescript
const note      = $peerText("note", "")                     // concurrent text edits
const visits    = $peerCounter("visits", 0)                 // commutative increments
const todos     = $peerList<Todo>("todos", [])              // ordered list with insert/remove
const settings  = $peerState<Settings>("settings", {...})   // general JSON-shaped state
```

Each is a `Signal<T>` with the same interface. The difference is in how Polly translates an assignment into a CRDT operation underneath. `$peerState` on a JSON object runs a structural diff against the previous value and applies a patch inside an `Automerge.change` block. `$peerText` captures insertions and deletions at the character level and forwards them to an Automerge text type. `$peerCounter` treats assignment as a delta from the previous value and forwards to a counter type. `$peerList` uses structural diffing over array identity to produce insert/remove operations with stable positions. In every case, the developer writes signal code and Polly produces correct CRDT operations.

The guarantees the primitive makes are strong and should be stated directly. Every replica that has received the same set of writes holds equal state. Every write is eventually delivered to every connected replica. A replica that reconnects after offline operation converges with the rest without developer action. A replica that rejoins after total data loss converges with the rest provided at least one other replica retains history. Schema migration is a first-class operation with verified semantics. None of these are aspirational; they are things Polly's TLA+ specification for the primitive must prove.

Options:

```typescript
const notes = $peerState<Notes>("notes", defaults, {
  sign: true,      // every op carries an Ed25519 signature; Byzantine defence
  access: {
    read:  identity => identity.userId === ownerId,
    write: identity => identity.userId === ownerId,
  },
  schemaVersion: 3,
  migrations: { /* ... */ },
})
```

`sign: true` adds per-operation Ed25519 signature verification, which defends against a compromised client pushing malicious writes that the relay would otherwise broadcast unchecked. The option is off by default because the common case is a collaborative app that trusts the Polly infrastructure and does not need Byzantine tolerance. Signing is enabled at the transport level via `createPeerStateClient({ sign: true, keyring: ... })` and validated at the primitive level — setting `sign: true` on a primitive whose Repo does not have signing enabled throws a clear error directing the developer to the transport configuration.

## Library choice

Automerge-Repo is the closer fit for Polly. Its `Repo` and `DocHandle` abstractions map cleanly onto "named state trees synced between peers," which is the job Polly's existing primitives already do. Documents are JSON-shaped, which plays well with the TypeScript interfaces developers already write. The library ships a stock `WebSocketClientAdapter`, a `NodeWSServerAdapter`, and an `IndexedDBStorageAdapter`, all of which drop into Polly's adapter pattern without reshaping it. Yjs wins on raw performance and bundle size and would be the right choice if collaborative rich-text editing became a primary workload, but for structured state the document-centric model matters more than the benchmark delta.

Automerge's own correctness rests on formal proofs in the CRDT literature. Polly does not need to re-derive them. What Polly's TLA+ must verify is the protocol around Automerge — the transport, the authorisation gate, the reconnect flow, the migration protocol, and (when `sign: true` is set) the signature enforcement. This is what makes day-one verification tractable.

## The transport

Clients connect to a WebSocket endpoint on the Polly server. The server hosts an Automerge-Repo `Repo` using `NodeWSServerAdapter` and persists to disk via `NodeFSStorageAdapter`, with Litestream streaming the volume to object storage for durability. Clients persist locally via `IndexedDBStorageAdapter`. When a client registers a document, Automerge's sync protocol exchanges compressed op sets between the client and the server until both hold the same heads; when either side mutates, the protocol incrementally propagates the delta. The server is a full replica participating in the same sync protocol as every client, which is what makes the resilience story work.

A new `PeerRelayAdapter` implements the new `CrdtNetworkAdapter` interface (distinct from the existing `SyncAdapter`, which continues to serve `$sharedState`) and wraps `WebSocketClientAdapter`. A new `peerRepo` Elysia plugin registers the server-side route at `/polly/peer`, distinct from the existing `/polly/ws` route. The existing plugin is untouched. Server-side code — cron, HTTP handlers, background tasks — mutates documents by opening handles on the server's `Repo`, which propagates changes through the same sync protocol.

This transport is deliberately small. One WebSocket route. One authorisation point. One durable store. The smallness is what makes the TLA+ specification tractable on a first pass and what makes the operational story legible. A developer deploying a `$peerState` application deploys one thing — the Polly Elysia app, on Railway or wherever — and that one thing handles every document, every client, every cron job, and every HTTP handler.

## Resilience

Resilience is the reason `$peerState` exists, and it deserves real treatment.

**Client offline, server online.** The default case. Writes happen against the local IndexedDB-backed replica and queue as Automerge ops. On reconnect, the sync protocol exchanges state vectors and delivers missing ops in both directions. No developer action; no data loss; guaranteed convergence.

**Client online, server temporarily offline.** Writes still happen against the local replica. The client's `PeerRelayAdapter` reconnects with exponential backoff. Pending ops flush on reconnect. Other clients on the same network see stale state until the server returns, but their own local mutations continue against their own replicas.

**Server total data loss.** The server volume is gone; Litestream restore failed or was not configured. This is the case that must not corrupt state. When the server comes up empty, it starts an empty `Repo`. The first client to reconnect performs a standard Automerge sync against the empty server, which means every op in the client's history is pushed to the server. The second client to reconnect syncs against the now-partially-populated server, pushing any ops the first client did not have. After every client has reconnected at least once, the server holds the union of every client's history, which is the correct recovery state.

The failure mode here is a client that has compacted its local history before the server lost its data. Compacted clients cannot replay ops the server is missing; they can only push their current state. If two compacted clients hold divergent current states because some ops lived only on the server, those ops are lost. Polly therefore treats compaction as a verified operation with strict preconditions: a client may only compact ops whose presence on the server is confirmed, and confirmation must be recorded in local storage before the op is dropped. This is exactly the kind of invariant TLA+ is good at proving and exactly the kind of invariant a hand-written distributed system gets wrong.

**Partition.** Automerge tolerates partition by design. When two sets of replicas cannot reach each other, each set continues to make progress locally. When the partition heals, the sync protocol merges. The CRDT guarantees strong eventual consistency: every replica that has seen the same set of ops holds the same state, regardless of partition history.

**Schema skew.** Two clients are running different application versions. The older client writes against an older schema; the newer client has migrated. Without defence, the older client's writes corrupt the document. With defence, the primitive rejects operations whose declared schema version is lower than the document's current version, and Polly surfaces a structured error the application can use to prompt the user to upgrade. The migration protocol in the next section handles the other direction.

**Byzantine peers.** By default `$peerState` does not defend against a compromised client pushing malicious writes. The server receives the writes, has no signature to verify, and broadcasts them to other clients. This is the trust model `$peerState` assumes by default — that clients are trusted, or that the application layer is responsible for whatever trust decisions it needs. Applications that need Byzantine defence set `sign: true`, which makes every op carry an Ed25519 signature verified by the server's share policy and by every receiving client. Revocation of a compromised key is itself a signed operation merged through the CRDT. Applications that need defence plus privacy from the server itself use `$meshState` instead, which builds both in by construction.

**History growth.** Automerge op history grows monotonically. Compaction (`Automerge.save`) produces a snapshot and drops history, at the cost of losing the causal record. Polly ships a compaction operation with the preconditions described above and a configurable policy — compact documents older than N days, or compact when history exceeds M operations — so that applications do not implement their own.

Every behaviour in this section is a candidate for the TLA+ specification. The next section treats that directly.

## Authorisation

Authorisation for `$peerState` happens at the WebSocket upgrade and at the document share policy. The upgrade handler validates the session cookie using the existing Polly auth hook and attaches the authenticated identity to the connection. The `Repo`'s share policy is a predicate over `(peerId, documentId)` that consults the identity and decides whether to announce the document. Polly provides a declarative authorisation API on top of this:

```typescript
$peerState<Settings>("settings", defaults, {
  access: {
    read:  identity => identity.userId === ownerId,
    write: identity => identity.userId === ownerId,
  },
})
```

The framework translates the `access` object into a share policy and enforces it inside the server-side `Repo`. Developers never write a share-policy callback directly, and the enforcement is part of the verified protocol.

With `sign: true`, the authorisation API is extended: the `access` object can name a set of public keys and the server additionally verifies every incoming op against that set before broadcasting. A compromised client that pushes unsigned or wrongly-signed ops is rejected at the server. Verification is also performed on receipt by other clients as defence in depth.

Encryption is not offered on `$peerState`. Encrypting sync messages would prevent the server from parsing them as Automerge protocol, which means the server could no longer maintain its own replica, run cron, or serve HTTP handlers — it would degenerate into a dumb message relay, which is exactly the role `$meshState`'s signalling server already fills. Applications whose threat model requires the server not to see document contents should use `$meshState`, which is designed for that posture from the ground up.

## Schema evolution

Schema evolution is a protocol, not a per-application concern, and the protocol needs to be verified.

Every `$peerState` document carries a schema version in a reserved field. Every application declares a migration table keyed by version number, where each entry is a pure function that transforms a document at version N into a document at version N+1. Migrations are required to be total — the function must accept any valid document at version N — and required to be deterministic — running the migration twice produces the same result. These constraints are checkable by Polly and can be enforced at development time.

On document load, Polly compares the stored schema version with the application's declared version. If the stored version is lower, Polly runs each pending migration inside an `Automerge.change` block, writes the migrated document back, and proceeds. If the stored version is higher, Polly refuses to load and surfaces a structured error: the application is older than the document.

Concurrent writes during migration are the genuinely hard part. Client A migrates to version 5; client B is still at version 4 and writes against the old schema. When B's write reaches the document, the CRDT would naively merge a v4 change into a v5 document, which is wrong. Polly's protocol defence is that every op carries the schema version under which it was produced, and ops at a lower version than the document are rejected at sync time. B receives a structured sync error, at which point B upgrades and replays against the new schema, or the application surfaces the error to the user.

This is a strong enough protocol to specify and verify. The TLA+ model is: a document with a schema version, N peers each with a local schema version, op delivery, version-mismatch rejection, and a convergence property stating that all peers eventually reach the same schema version and the same document state. Exactly the kind of property Polly's existing TLA+ work is equipped to prove.

## TLA+ verification

The existing Polly TLA+ spec at `verification/tools/verify/specs/tla/MessageRouter.tla` verifies routing properties for a single-writer messaging system. A peer-first spec is a different model, and it is a day-one deliverable, not a deferred milestone. The point of this RFC is that Polly's value lies in making hard things easy through verified abstractions — shipping `$peerState` without the verification is shipping the hard part without the Polly.

The spec models N replicas, each holding a document at some schema version, a server replica with persistent storage, a sync protocol that exchanges ops between replicas, an authorisation predicate at the server, and a migration protocol. The properties to verify are:

- **Strong eventual convergence.** Any two replicas that have received the same set of ops hold equal state. This is inherited from Automerge's proofs but must be re-expressed in the TLA+ model so it composes with the other properties.
- **Authorisation soundness.** A replica that the authorisation predicate rejects cannot observe or influence document state. No sync message leaks document contents past the share policy.
- **Migration convergence.** All replicas eventually reach the same schema version, and the resulting document state is the same regardless of the order in which migrations and user ops are interleaved.
- **Recovery convergence.** After a server data loss event, provided at least one replica retains full history and has not compacted, every reconnecting replica eventually observes the union of all replicas' histories.
- **Compaction safety.** A replica may only drop op history whose presence at the server is confirmed; compacted replicas cannot lose ops that existed only on the server.

The `sign: true` option does not add new properties to this spec. Signature soundness, revocation convergence, and the other signing properties are covered by the `$meshState` TLA+ spec, because the underlying signing machinery is the same code path (`MeshNetworkAdapter` in sign-only mode). A `$peerState` document with `sign: true` is verified against the same signing properties as a `$meshState` document; the difference is in the transport-level properties (recovery convergence differs between relay and mesh).

Each property is a real failure mode if Polly gets the protocol wrong. Each is the kind of guarantee the developer inherits by writing `$peerState` and reading `.value`, which is the whole point.

## First milestone

1. `$peerState`, `$peerText`, `$peerCounter`, `$peerList` primitives with the API shape above. No escape hatches. `sign` option wired to the `MeshNetworkAdapter` sign-only mode via `createPeerStateClient`.
2. `PeerRelayAdapter` implementing the new `CrdtNetworkAdapter` interface, wrapping `WebSocketClientAdapter`.
3. `peerRepo` Elysia plugin exposing `/polly/peer`, hosting a server-side `Repo` with `NodeFSStorageAdapter` and Litestream.
4. Declarative `access` option compiling to a share-policy enforcement layer.
5. Schema-version plumbing, migration registry, sync-time version check, structured error on version mismatch.
6. TLA+ specification covering the five properties above, with TLC model-checking configuration, as part of the same milestone as the code.
7. Compaction operation with the precondition invariant verified by the TLA+ spec.

Out of scope for this primitive: any actual blob storage or large-file sync (see the follow-up RFC), tab-to-tab `BroadcastChannel` sync, and migration of existing `$sharedState` consumers. The `$meshState` primitive is a coordinated sibling milestone in [RFC-041-peer-first-webrtc.md](./RFC-041-peer-first-webrtc.md); it ships alongside this one, and the shared crypto machinery it builds is what powers the `sign` option here.

## Open questions

1. **Diff granularity for `$peerState`.** A structural JSON diff is the obvious implementation but it has edge cases (array reordering, object key renames, deep vs shallow). The alternative is requiring `$peerState` to wrap a known shape and using Automerge's native ops at each leaf. Which gives better DX, and which is easier to verify?
2. **Counter semantics.** `$peerCounter` assigned as `counter.value = counter.value + 1` needs to compile to a commutative increment, not a last-write. The signal assignment has to be interpreted relative to the previous value, which is a reactive-programming corner case. Is there a cleaner API, e.g. `counter.increment(1)`, that keeps signal semantics?
3. **List reordering.** `$peerList` with a user-triggered reorder of two existing items is not obviously diffable to a CRDT operation. Does Polly ship a `list.move(from, to)` method, or does it diff and produce a move op automatically?
4. **TLA+ state explosion.** The peer-first spec has a larger state space than the existing routing spec. Is TLC sufficient with bounded model sizes, or does this need Apalache?
5. **Bundle size.** Automerge's WASM core adds roughly a couple of hundred kilobytes gzipped. Can `$peerState` be lazy-loaded so that applications not using it pay nothing?
6. **Server-side mutation identity.** When cron code mutates a document through the server's `Repo`, who is the writer from an authorisation perspective? The server's own session, a dedicated system identity, or something else? The answer shapes the share-policy language, especially with `sign: true`.
