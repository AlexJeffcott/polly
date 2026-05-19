# RFC-041 (addendum) — Choosing among Polly's synced state primitives

Tracking issue: [AlexJeffcott/polly#41](https://github.com/AlexJeffcott/polly/issues/41)

Status: addendum to the RFC-041 design. See the two peer-first proposals in [RFC-041-peer-first.md](./RFC-041-peer-first.md) (`$peerState`, server-as-peer) and [RFC-041-peer-first-webrtc.md](./RFC-041-peer-first-webrtc.md) (`$meshState`, server-off-the-data-path).

This document answers three questions the primitive proposals leave open. What does Polly ship — one new primitive, two, or none? How does a developer choose among the alternatives? And what happens when an application mixes them in one codebase?

## The three primitives, ordered by resilience

The decision the developer is making is about resilience: how bad does it have to get before this data is unrecoverable? Polly offers three answers, ordered from weakest to strongest.

**`$sharedState` — server is the source of truth.** The existing primitive. A canonical state lives on the server, broadcast to clients over a WebSocket, with Lamport-clocked last-write-wins for conflict resolution. Clients are views with optimistic local writes that reconcile on reconnect. Resilience is whatever the server's backup story is: lose the server badly, lose the data. This is the right primitive when the application has a natural source of truth on the server — a public API, a multi-tenant SaaS, anything where the meaningful question is "what does the server say."

**`$peerState` — server is a peer on the data path.** The first of the two new primitives. Every device is a full Automerge replica, and the Polly server holds a replica too. Conflicts merge through the CRDT, and the server participates in the sync protocol as an ordinary peer that happens always to be on. Server-side code can open document handles and operate directly on document contents — cron, HTTP handlers, scheduled jobs, aggregation, indexing. Any device loss is recoverable from any other device, including recovery of the server itself from its clients' local histories. `sign: true` adds per-operation Ed25519 signatures for audit trails and compromised-client defence without preventing the server from reading document contents. Encryption is not offered on `$peerState` — applications that need the server not to see contents should use `$meshState`.

**`$meshState` — server is not on the data path.** The second new primitive. Every device is a full Automerge replica; the server is not. Clients find each other through a small stateless signalling endpoint and open direct WebRTC data channels. Document operations flow peer-to-peer and never touch the server. If the server were permanently gone, the application would still function — peers already know about each other and continue to sync. Signing and encryption are mandatory, not options, because the trust model requires them. Cron jobs that need to operate on `$meshState` data run on a dedicated always-on peer that is itself a full client, deployable anywhere, and never special.

The three primitives are strictly ordered: `$meshState` is more resilient than `$peerState`, which is more resilient than `$sharedState`. The developer's question is "how bad does it have to be before this data is unrecoverable," and the answers climb a ladder.

Each primitive has specialised variants for data shapes that do not diff naively: `$peerState` pairs with `$peerText`, `$peerCounter`, `$peerList`; `$meshState` pairs with `$meshText`, `$meshCounter`, `$meshList`. All are signals at the call site; the specialisation is entirely about how Polly translates assignments into CRDT operations underneath.

## Which of these does Polly ship

Three options for the first release of RFC-041.

| Option | What ships | What is missing |
|---|---|---|
| A — all three | `$sharedState` + `$peerState` + `$meshState` | — |
| B — current + `$peerState` | `$sharedState` + `$peerState` | No answer for applications whose resilience story requires zero server dependency |
| C — current + `$meshState` | `$sharedState` + `$meshState` | No answer for applications that need server-side compute on peer-replicated data |

**Option A is the right answer**, and the rest of this document treats it as the decision.

The three primitives are not substitutes for each other. Each answers a different resilience question, and dropping either of the new ones forces developers with that resilience story to misuse a primitive designed for a different one. Option B has no answer for an application that needs to function when the server is permanently unreachable. Option C has no answer for a cron job that needs to read and summarise a shared document. Both are workloads Polly's existing users already have.

The incremental cost of shipping both new primitives together is smaller than it looks. The `$meshState` TLA+ specification is a superset of the `$peerState` specification — it covers every convergence, recovery, and migration property of the relay model, plus signature soundness, revocation convergence, and privacy soundness. The hard verification work happens once. The two transports share the primitive layer, the CRDT library, the client-side storage adapter, the declarative `access` API, the schema-version migration protocol, and the majority of the test suite. The crypto machinery built for `$meshState` is also what powers the optional `sign` path on `$peerState` (via `MeshNetworkAdapter` in sign-only mode), so the work is reused rather than duplicated.

Shipping only one of the two new primitives and adding the other later forces every application that picked the wrong one into a migration. Shipping both together lets applications pick per document on day one.

## How a developer chooses

Three yes/no questions. They concern resilience — not topology, privacy, or performance — and the developer can answer them without knowing how any of the transports work.

**Is the server the source of truth for this data?**
Yes → `$sharedState`. The canonical state lives on the server, and the application's job is to keep clients in sync with it. This is the existing primitive and it is unchanged by RFC-041.

No — every device should hold a full replica and recover from any other device. Continue.

**Should the application function if the server is permanently gone?**
Yes → `$meshState`. Every client already holds the full document, peers already sync directly, and no central process is needed for the data to keep flowing. The signalling server, if it exists, is small and replaceable.

No — the server stays on the data path, because server-side code (cron, HTTP handlers, scheduled jobs) needs to read or mutate the document. Continue.

→ `$peerState`. Every device is a full replica, the server included. The server's loss is a rebuild from any reconnecting client, not a disaster. Cron and server-side compute work because the server can read and mutate the document like any other peer.

That is the entire decision. Three questions, three primitives, answerable from the application's resilience requirements rather than any detail of the implementation.

A comparison table, for the developer who wants to sanity-check the choice:

| Property | `$sharedState` | `$peerState` | `$meshState` |
|---|---|---|---|
| Conflict resolution | LWW with Lamport clock | CRDT (Automerge) | CRDT (Automerge) |
| Server holds replica | Yes (authoritative) | Yes (peer) | No (signalling only) |
| Server reads plaintext | Yes | Yes | Never |
| Server runs cron on contents | Yes | Yes | No (use dedicated cron peer instead) |
| App functions with server permanently offline | No | Degraded (no cron, no new-client onboarding) | Yes |
| Recovery from total server loss | Data loss without backup | Rehydrate from any client | Nothing to recover — server holds nothing |
| Byzantine tolerance | No | Optional (`sign: true`) | Yes (mandatory) |
| E2E encryption | No | No (use `$meshState`) | Yes (mandatory) |
| Operational complexity | Low | Medium | High (TURN, signalling, key management) |
| TLA+ verified | Routing layer only | Yes (day one) | Yes (day one) |

## Why distinct primitives instead of `$peerState` with a `transport` option

Semantically, the two new primitives differ in what server-side code can and cannot do with the data. With `$peerState`, the server holds a replica and server-side code can mutate it. With `$meshState`, the server holds nothing meaningful and server-side code cannot import the primitive at all. That is not configuration; it is contract.

Distinct primitives buy three things a configuration field cannot.

**Static enforcement on the server.** `$meshState` has no meaningful implementation server-side: it cannot decrypt its own documents and cannot produce valid peer signatures without a device keypair. Shipping it as a separate export lets Polly omit it entirely from the server-side bundle, so server code that tries to import it is a build error rather than a runtime surprise. A `transport` option on a single primitive cannot express that constraint to the type system.

**Type-level discoverability.** Autocomplete in an editor surfaces three primitives. A developer who has never read the RFC sees them and infers the distinction from the names. An options object on a single primitive hides the decision inside a generic bag.

**Distinct options shapes.** `$peerState` takes `sign` as an optional flag; `$meshState` does not, because it always signs and always encrypts. `$peerState` does not offer `encrypt` at all — encrypting sync messages would prevent the server from parsing them, which defeats the purpose of having the server on the data path. Expressing these differences cleanly in the type system is much easier with distinct primitives than with a discriminated union hanging off a transport enum.

## Mixing primitives in one application

Mixing the three primitives inside one application is expected, not an edge case. Different pieces of data in the same application typically have different resilience requirements, and the three primitives exist to let a developer express "this is public and server-owned, this is collaborative and recoverable, this needs to survive the server entirely" without reaching for heroics.

**Safe patterns.** These are the ones Polly encourages.

- Public settings in `$sharedState`, collaborative working documents in `$peerState`, personal notes in `$meshState`. Three transports, three storage paths, no interaction. The developer picks per signal and Polly keeps the data completely separate.
- A collaborative document in `$peerState` with a cron job that summarises it into a `$sharedState` dashboard. The cron reads the peer document from the server and writes the dashboard authoritatively. This pattern is exactly why `$peerState` exists.
- `$peerState` metadata pointing at `$meshState` contents. The peer document holds titles, timestamps, and an opaque reference to a mesh document; the mesh document holds the body. The server can index and schedule against the metadata but has no way to read the body.

**Unsafe patterns, and what Polly enforces.**

- **Key collision across primitives.** `$sharedState("notes")` and `$peerState("notes")` are two different documents stored in two different places with no sync between them. A developer who expects them to be the same data will be badly surprised. Polly namespaces storage keys by primitive internally and refuses at runtime to register the same logical key under more than one primitive, with a structured error that names both call sites.
- **Type confusion across primitives.** The three primitives serialise differently: LWW value plus clock, Automerge ops, encrypted and signed Automerge ops. The on-disk formats are incompatible. Polly never silently coerces between them; migration is an explicit one-way operation (see below).
- **Server-side access to `$meshState`.** Server code that imports `$meshState` is a type error. Polly ships the server bundle without the primitive at all and the client bundle with it. A cron job that needs to touch a document must use `$peerState` for that document; the decision is forced on the developer rather than hidden.
- **Authorisation drift.** The declarative `access` API is shared where the semantics overlap — `read` and `write` as predicates over peer identity — and diverges where it has to. Only `$meshState` consumes encryption keys, because only the mesh transport encrypts. The type system makes the difference visible at every call site that uses `access`.
- **Cross-primitive transactions.** There are none. A write that must update `$sharedState` and `$meshState` atomically has to be modelled by the application, because no single transport spans both. Polly does not offer distributed transactions across transports and will not pretend to. The guidance is to pick primitives such that each logical atomic unit lives entirely within one.
- **Cross-transport cron.** A cron job on the Polly server can read and write `$sharedState` and `$peerState` but cannot read or write `$meshState`. This is the whole point of the third tier. A developer who wants cron to operate on data must not put that data in `$meshState`; the enforcement is at the type level rather than a runtime surprise. Applications that truly need cron on `$meshState` data run a dedicated cron peer — a separate Node process with its own device keypair that participates in the mesh as an ordinary client and happens never to sleep.

## Migration between primitives

Moving data from one primitive to another is a deliberate, one-time, application-authored operation. Polly ships a helper:

```typescript
await migratePrimitive(
  $sharedState<OldNotes>("notes"),
  $meshState<NewNotes>("notes", { entries: [] }),
  old => ({ entries: old.entries ?? [] }),
)
```

The helper reads the source's current value, runs the application's transform, writes the result into the destination, and marks the source as migrated in a local registry so that subsequent reads from the source fail loudly rather than silently returning stale data. It is invoked explicitly on upgrade, once per device, and it is not a substitute for the schema-version migration protocol within a single primitive.

Migration between the new primitives is possible but thoroughly one-way. `$peerState` documents can be migrated to `$meshState` by encrypting and signing every op on the client; the reverse, `$meshState` to `$peerState`, requires the application to decrypt client-side and push the plaintext to the server, which loses the encryption guarantee by construction. Downgrade to `$sharedState` is not supported in general, because the CRDT history has no lossless LWW projection.

## What ships together

All three primitives in one release, with the mixing rules enforced from day one and the migration helper available from day one. The two transport proposals in `RFC-041-peer-first.md` and `RFC-041-peer-first-webrtc.md` have their own design documents and their own first milestones, but those milestones are coordinated: the primitive layer, the CRDT layer, the declarative `access` API, the storage layout, the schema-version protocol, the migration helper, and the enforcement of the mixing rules are all shared work. The `$peerState`-specific work is a WebSocket route, a `Repo` hosted on the Polly server, and a share policy. The `$meshState`-specific work is a signalling plugin, a signed-op adapter, a pairing flow, and key management. These are additive surfaces on top of a common primitive layer.

The guiding principle for the release is the principle that drove the TLA+ work: Polly exists to carry the hard parts so that its users do not have to. Every hard part Polly does not carry is a hard part the application layer has to re-solve for itself. Shipping two of the three resilience tiers and calling the third a future milestone would leave one of those hard parts outside the framework, and leave the developer picking a primitive they do not actually want because the one they want does not exist yet.
