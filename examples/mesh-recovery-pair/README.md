# mesh-recovery-pair

Runnable demonstration for polly issue #103 — the "long-lived daemon
pairs a new device, peers stay at zero" contract violation.

## What this example shows

Two werift-backed mesh peers wired up against an in-process polly
signalling server, configured in the failing-shape diff from the
parent ticket:

- **Peer A** (the daemon) starts with **10 unrelated `knownPeers`**
  entries from prior pairings — the "82 priors" condition from the
  ticket, narrowed to the ticket's minimum bar (`≥ 5`) so the run is
  fast.
- **Peer B** (the receiver) starts with a single `knownPeers` entry —
  peer A — modelling a freshly-recovered-identity device.
- Peer A's mesh client is constructed **before** peer B is folded into
  A's keyring. After a 250ms gap (modelling the signalling-roundtrip +
  user-scanning-QR delay in the real fairfox flow), peer A's keyring
  is mutated in place with a peer-B pairing token — the
  daemon-running-while-pairing shape.
- A per-run sentinel string is written into peer A's `$meshState`
  document **before** any data channel can form. The nonce is unique
  to this process — no cached browser state could pre-contain it — so
  the only way for B's local replica to satisfy the assertion is for
  Automerge sync to actually traverse the mesh.

## Running it

```bash
cd examples/mesh-recovery-pair
bun install
bun run main.ts                              # post-fix path (default)
POLLY_103_DISABLE_FIX=1 bun run main.ts      # reproduces pre-fix failure
POLLY_103_TRACE_VERBOSE=1 bun run main.ts    # dumps every snapshot frame
```

Exit code is `0` on contract satisfied, `1` on contract violated, `2`
on refusal under a false-positive condition.

## What the two modes look like

**post-fix** — the polly `MeshClient` reads `knownPeers` live from
the keyring and re-sweeps the signalling roster every two seconds, so
the entry added by `applyPairingToken` is picked up on the next sweep:

```
[result] SUCCESS — contract holds: data channel open, sync bidirectional, sentinel propagated
```

**pre-fix-emulated** — passing `knownPeersRefreshIntervalMs: 0`
disables the sweep, leaving polly in the captured-set shape that
shipped in `0.52.0`. The adapter never re-evaluates `shouldInitiateTo`
for peer B and the deadlock holds for the lifetime of the process:

```
[result] FAILURE — contract violated. A.sawPeer=false B.sawPeer=false
                   sentinel-on-B=false slot-connected=false dc-open=false
```

The `[snapshot]` line one above the result shows the giveaway: peer A
sees peer B in both its keyring and the signalling roster, but holds
no slot for peer B at all. The dial step never ran.

## What this example is not

The polly internal integration test
(`tests/integration/mesh-recovery-pair-stale-known-peers.test.ts`)
runs the same shape against `bun:test`, so the contract assertion
lives in CI without depending on a chromium download. Use this
example as the **visible** transcript and use the test as the
binary pass/fail in polly's own pipeline.

This example does not yet exercise the **real Chrome 148 + browser
recovery-blob ingestion** surface from the parent ticket. The
werift-on-both-sides shape isolates polly's framework-layer bug
(stale `knownPeers` after post-construction `applyPairingToken`);
the browser-specific layers — service worker storage, IndexedDB,
hash-fragment pair-return — sit outside polly and are exercised by
downstream consumers' own e2e harnesses.

## Refusal gates

The example refuses to run with exit code `2` if any condition that
the parent ticket lists as a known false-positive surface is
detected:

- CLI-side keyring would have fewer than 5 `knownPeers` entries
- CLI-side mesh storage would be empty
- Browser-side identity would be fresh (rather than recovery-blob)

These checks live in `refuseIfFalsePositiveConditions` near the top
of `main.ts` and run before any peer is constructed. They are the
ticket's item 4 reified — the harness exists because the original
e2e passed under exactly these conditions while the real consumer
flow was broken.
