# mesh-recovery-pair

Runnable demonstration for polly issue #103 — the "long-lived daemon
pairs a new device, peers stay at zero" contract violation.

This example carries two artefacts that both claim the polly#103
contract holds, but by different means:

- `main.ts` — a wire-level falsification harness that pairs two
  werift-backed mesh peers against an in-process polly signalling
  server and asserts the contract over the live transport.
- `src/`, `specs/verification.config.ts` — an abstract state-machine
  model of the same race, encoded as polly handlers with
  `requires`/`ensures` postconditions, suitable for `polly verify` to
  explore with TLC.

Neither subsumes the other. The wire-level harness exercises the
real Automerge, WebRTC, and signalling stacks but only checks the
single interleaving the test ran. The verifier explores every
ordering of the modelled events within the bounded depth but
abstracts away the transport. They are complementary evidence.

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

## The verifier model

`src/state.ts` declares six boolean flags that together capture the
observable state of the race:

| Flag              | Meaning                                                                    |
| ----------------- | -------------------------------------------------------------------------- |
| `aRosterHasB`     | Peer A's signalling roster has reported peer B online.                    |
| `aKeyringHasB`    | Peer A's `MeshKeyring` contains peer B's signing key.                     |
| `aAdapterKnowsB`  | Peer A's `MeshWebRTCAdapter.knownPeers` Set contains peer B. **The bug surface.** |
| `dataChannelOpen` | The WebRTC data channel between A and B is open.                          |
| `sentinelWritten` | Peer A has written the per-run sentinel into its `$meshState` document.   |
| `sentinelObserved`| Peer B's local replica has observed the sentinel.                         |

`src/handlers.ts` registers five message handlers — one per wire-level
event — and chains them via `requires` preconditions:

```
ROSTER_PEER_JOINED  →  APPLY_PAIR_TOKEN  →  OPEN_DATA_CHANNEL
                    →  WRITE_SENTINEL    →  RECEIVE_SENTINEL
```

The polly#103 contract is the `ensures` clause on `APPLY_PAIR_TOKEN`:

```ts
ensures(
  aAdapterKnowsB.value === true,
  "polly#103: applying the pair token must refresh the adapter knownPeers"
);
```

The fix is a single line inside the same handler — `aAdapterKnowsB.value
= true` — marked `POLLY_103_FIX` in the source. Comment that line out,
re-run `polly verify`, and TLC produces the counterexample:

```
❌ Verification failed!
Error: Action property EnsuresAfter_HandleApplyPairToken is violated.
```

The trace in `specs/tla/generated/tlc-output.log` shows the failing
interleaving: `ROSTER_PEER_JOINED` delivered, then `APPLY_PAIR_TOKEN`
delivered, then the post-state has `aKeyringHasB = TRUE` but
`aAdapterKnowsB = FALSE` — exactly the keyring-vs-adapter divergence
polly#103 fixed. Restore the line, re-run, watch it pass (8 distinct
states).

## Running the verifier

```bash
cd examples/mesh-recovery-pair
bun install                # postinstall fixes the @fairfox/polly link
polly verify               # if polly is on PATH
# or, from inside the repo:
bun ../../dist/cli/polly.js verify
```

## What this verifier model does and does not prove

The model is an **abstract state machine over six booleans**. It
proves the polly#103 contract holds across every reachable
interleaving of the modelled events under the bounded depth, given
the temporal constraint that the roster reports B before the pair
token lands. It does **not** model:

- The actual Automerge merge semantics. `$meshState` propagation here
  is a single boolean toggle; concurrent writes, conflict resolution,
  and CRDT-internal seeding (see polly#113) are out of scope.
- Real WebRTC negotiation. ICE, DTLS, SCTP substates collapse into
  one `dataChannelOpen` bit.
- Network non-determinism beyond polly's existing `MessageRouter`
  model. No partition, no loss, no reorder beyond FIFO.
- The factory-wiring class of bug from polly#57 / polly#107. Those
  live in construction paths the verifier cannot see — `main.ts` is
  the right evidence for that class.

The wire-level harness in `main.ts` covers what the verifier cannot;
the verifier covers what wall-clock single-run e2e cannot. The point
of having both is that neither alone is sufficient to claim the
contract holds.

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
