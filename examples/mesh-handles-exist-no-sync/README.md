# mesh-handles-exist-no-sync — falsification harness for polly issue #107

The diagnostic ladder polly#106 shipped for the `lastSyncHandshakeAttempt`
snapshot named "no handle locally" as the typical cause for the rung
where `peerCandidateEmittedAt` is set and `firstOutboundSendAt` is
undefined. The polly#107 failing-shape evidence (real Chrome 148 tab
paired against a Fly-hosted daemon, fourteen `$meshState` handles
pre-warmed before the WebRTC slot opens, every handle in `ready` state
in `repo.handles`) demonstrates that the ladder pointed at the
consumer for a case the consumer cannot fix.

This harness exercises the documented entry point applications use —
`$meshState(key, initial)` — across two werift peers on a local
signalling server. It is the load-bearing regression guard for the
polly#107 observability layer (per-peer per-handle
`{ state, announcedToPeer, lastSyncMessageOutAt, ... }`) and the
peer-candidate-triggered `reevaluateDocumentShare` hook on the mesh
client.

## What the harness asserts

1. Both peers construct **fourteen** `$meshState<MeshDoc>` wrappers
   via the documented factory entry point. Earlier polly examples
   exercise `repo.import()` directly, which sidesteps the wrappers'
   lazy `getHandle()` factory path — precisely the path the
   polly#107 production report says is the failure surface.
2. Every wrapper's `loaded` promise resolves and the handle is in
   `ready` state in `repo.handles` **before** `peer-candidate` fires
   on the slot.
3. After `peer-candidate` fires, the sender's content sentinel
   propagates to every receiver `$meshState.value` within a budget
   that scales with handle-count.
4. The receiver's `getPeerStateSnapshot()` shows
   `firstOutboundSendAt` populated AND every handle's enriched view
   has `announcedToPeer: true`.

## Wire-level transcript

`transcript.json` (written at the end of every run) lists per-peer
per-handle: `state`, `announcedToPeer`, `lastSyncMessageOutAt`,
`lastSyncMessageOutSize`, `lastSyncMessageOutType`,
`lastSyncMessageInAt`. Post-fix runs show every pre-warmed handle
announced; a future regression that introduces a gap in any field is
visible by diff.

## Running

```sh
bun install
bun run main.ts                              # post-fix path
POLLY_107_DISABLE_FIX=1 bun run main.ts      # falsification mode
POLLY_107_TRACE_VERBOSE=1 bun run main.ts    # dump every snapshot sample
```

## Refusal gates

The harness refuses to run when:

- Fewer than 5 handles are pre-warmed (small-handle-count shape does
  NOT exercise the polly#107 surface).
- No peer is present in signalling at slot-open time (the failure
  requires an active remote with sync messages to send).
- Any pre-warmed handle in `repo.handles` is not in `ready` state at
  slot-open time (the polly#106 ladder explicitly named
  `state !== "ready"` as the consumer-fixable rung).

Exit code 0 on success, 1 on contract violation, 2 on refusal.

## Limitation — werift vs Chrome+Fly

The production failing-shape that polly#107 documents requires Chrome
148's specific data-channel timing against the deployed Fly stack and
~17 MB of CRDT history on the daemon side. werift on local loopback in
a single bun process does NOT reproduce that timing — the standard
Automerge flow's `addPeer`-iterates-docSynchronizers and
`addDocument`-iterates-#peers cross-paths handle the local case fine
with or without the polly#107 fix engaged.

What `POLLY_107_DISABLE_FIX=1` proves under werift:

- The gate flips the code path (the `reevaluateDocumentShare` hook on
  `peer-candidate` is not attached).
- The polly#107 observability layer is exercised on both code paths
  and produces identical wire-level transcripts — exactly because
  there is no bug to expose in werift. Any future regression that
  DOES break the local case would show up as a transcript diff.

Production validation of the actual fix lives in fairfox's Sync
diagnostics surface against the deployed Fly stack — the expected
snapshot shape after the fix is engaged is `firstOutboundSendAt`
populated on the slot and `announcedToPeer: true` on every entry of
the slot's `handles` map.
