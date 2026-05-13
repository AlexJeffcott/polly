# mesh-slot-initiation-realistic-keyring

Runnable demonstration for polly issue #106 — the "some `peer-joined`
notifications don't create a slot — and existing slots don't initiate
sync — against a real keyring with many priors" contract violation.

## What this example shows

A daemon-shaped polly mesh client wired up against an in-process
signalling server, with the realistic keyring shape the polly#106
ticket calls out:

- **Daemon keyring of 66 known peers** (`KEYRING_FILLER_COUNT = 60`
  filler + 6 real). The reporter's daemon held 78; the polly#103
  example held 10. The polly#106 ticket's refusal bar is `≥ 50`.
- **Six real peers** that actually appear on signalling: three arrive
  before the daemon connects (so they land via `peers-present`) and
  three arrive after (so they land via `peer-joined`). Gradual arrival
  is the polly#106 ticket's mandatory shape.
- **Mixed lex tie-break**: half the real peers are lex-lower than the
  daemon (daemon dials), half are lex-higher (real peer dials). The
  polly#106 ticket refuses runs where every peer sits on the same side
  of the daemon's id, because that masks one-direction tie-break bugs.
- **Synthetic-throw injection** on one real peer's slot construction.
  Models the realistic risk that `new RTCPeerConnection()` can throw
  under sustained load, hostile config, or per-page caps. The polly#106
  fix wraps every dial entry point in a per-peer try/catch; pre-fix
  code lets the throw bubble out of the signalling client's frame
  dispatch, killing the daemon process for every later peer in the
  same batch.

## Running it

```bash
cd examples/mesh-slot-initiation-realistic-keyring
bun install
bun run main.ts                              # post-fix path (default)
POLLY_106_DISABLE_FIX=1 bun run main.ts      # reproduces pre-fix failure
POLLY_106_TRACE_VERBOSE=1 bun run main.ts    # dumps every snapshot frame
```

Exit code is `0` on contract satisfied, `1` on contract violated, `2`
on refusal under a false-positive condition.

## What the two modes look like

**post-fix** — the polly `MeshWebRTCAdapter` wraps every dial entry
point in a per-peer try/catch and records the failure as
`slotInitiationRejectionReason: "fatal-error"` on the snapshot. The
sweep keeps running, the other peers get slots, and the failing peer
is named:

```
[outcome] b-real-peer-02       ... slotted=false reason=fatal-error ...
[sweep] sweep ran 34 times in 8000ms ... uncaught errors escaped: 0
[result] SUCCESS — every non-failing real peer got a slot, every connected
                   slot emitted peer-candidate AND issued an outbound send
                   through the adapter, and the failing peer's snapshot
                   names it with `fatal-error`.
```

**pre-fix-emulated** — `disablePerPeerTryCatch` overrides
`handlePeerJoined`, `handlePeersPresent`, and `refreshKnownPeers` with
versions that don't try/catch, mirroring the pre-#106 code. The
synthetic throw escapes:

```
[outcome] b-real-peer-02       ... slotted=false reason=(none) ...
[sweep] sweep ran 34 times in 8000ms ... uncaught errors escaped: 1
[result] SUCCESS — pre-fix-emulated path reproduced the failure: synthetic
                   throw aborted the sweep, downstream peers were never
                   dialled.
```

(The `SUCCESS` in pre-fix-emulated mode means "the harness reproduced
the ticket's failure shape" — i.e. it confirmed that polly without the
fix exhibits the contract violation. The `failureReason` field in
`transcript.json` is `null` in this case because the harness's job is
to *demonstrate* the failure, not to pretend the contract held.)

## Observability surfaces this exercises

The polly#106 fix added two new fields to `getPeerStateSnapshot()`:

- **`slotInitiationRejectionReason`** per peer: names which gate
  inside `shouldInitiateTo()` declined the dial — `not-in-keyring`,
  `not-present`, `tie-break-other-side`, `slot-already-exists`, or
  `fatal-error`. The example's outcome line prints this for every
  peer, so a snapshot reading "(no slot)" can be triaged without
  instrumenting polly.
- **`lastSyncHandshakeAttempt`** per slot: timestamps for when the
  data channel opened, when polly emitted `peer-candidate` upward,
  when Automerge first dispatched a send through polly's adapter, and
  when polly first emitted an inbound message upward. The example
  asserts that every connected slot reaches all four — proving the
  sync handshake actually started, not just that the wire opened.

The snapshot also exposes `sweep.runCount` and `sweep.lastRunAt` so a
debugger can rule out "sweep is dead" before chasing
`shouldInitiateTo` gates. The example's `[sweep]` line prints this.

## Refusal gates (polly#106 item 3)

Refuses to run with exit code `2` if any condition that the parent
ticket lists as a known false-positive surface is detected:

- Daemon keyring has fewer than 50 known peers (the polly#103 surface).
- Every real peer is online at signalling-join time (no gradual
  arrival).
- Every real peer is on the same side of the daemon's lex-tie-break
  (would mask an initiator/answerer-direction bug).

These checks live in `refuseIfFalsePositiveConditions` near the top of
`main.ts` and run before any peer is constructed.

## Wire-level transcript

`transcript.json` is written next to `main.ts` at the end of every
run. It includes the configuration, the per-peer outcome, the
captured uncaught-error count, and the full
`getPeerStateSnapshot()` from the daemon's perspective. The pre-fix-
vs-post-fix bisect is visible by diffing two transcripts: pre-fix has
`uncaughtErrorCount: 1` and the failing peer's
`slotInitiationRejectionReason` is the stale value from before the
throw; post-fix has `uncaughtErrorCount: 0` and
`slotInitiationRejectionReason: "fatal-error"`.

## What this example is not

This example exercises the polly framework layer — adapter dial paths
and snapshot observability. It does not exercise the **real Chrome
148 paired into a fly.io-deployed daemon** surface from the parent
ticket. The werift-on-both-sides shape isolates the framework bug;
the browser-specific surfaces (service worker, IndexedDB, real TURN)
sit outside polly and are exercised by downstream consumers' own e2e
harnesses.
