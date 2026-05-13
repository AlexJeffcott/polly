# mesh-large-initial-sync-turn

Runnable demonstration for polly issue #105 — the "polly#104 closed the
in-process throttled case but a fresh peer paired through a real TURN
relay still cannot consume a non-trivial initial sync" contract
violation.

## What this example shows

Two werift-backed mesh peers wired up against an in-process polly
signalling server **and a real TURN server** (a child Pion `turn`
process bound to a random UDP port on `127.0.0.1`), configured under
the failing-shape diff from issue #105:

- **Peer A** holds the same 5 MB Automerge document the polly#104
  harness uses, with the per-run UUID sentinel inside the payload.
- **Both peers** are configured with `iceTransportPolicy: "relay"`
  and an `iceServers` list pointing exclusively at the local Pion
  TURN endpoint. The harness refuses to run with any other policy.
- **The negotiated candidate pair must be (relay, *)** on at least
  one side's selected pair view, sourced from
  `RTCPeerConnection.getStats()` and exposed through polly's new
  `MeshClient.refreshTransportStats()` + the `transport` field added
  to `getPeerStateSnapshot()`. If ICE picks a non-relay path the
  contract is violated and the run exits non-zero.
- **All four polly#104 signals are still observed**: sentinel
  propagation end-to-end, `inFlightSync` chunks received mid-run,
  event-loop tick-gap probe, and per-peer `peer-candidate` arrival.
  None of polly#104's bar is relaxed for this harness.

## Running it

The Pion TURN server is a small Go program in `pion-turn-server/`.
Build it once before the first run:

```bash
cd examples/mesh-large-initial-sync-turn
bun install
bun run build:turn-server                                    # produces ./pion-turn-server/pion-turn-server
POLLY_105_TURN_MODE=real bun run main.ts                     # post-fix path (the `start` script wraps this)
POLLY_105_TURN_MODE=real POLLY_105_DISABLE_TURN_FIX=1 bun run main.ts   # reproduces pre-fix failure
POLLY_105_TRACE_VERBOSE=1 POLLY_105_TURN_MODE=real bun run main.ts     # verbose stderr
```

If the prebuilt binary isn't present the harness falls back to
`go run .` from inside `pion-turn-server/` — slower first start but
no separate build step.

Exit code is `0` on contract satisfied, `1` on contract violated,
`2` on refusal under a false-positive condition.

## What the two modes look like

**post-fix** (default) — polly's new ICE relay-only enforcement layer
filters non-relay candidates out of both the SDP it forwards and the
trickle ICE stream it emits, on top of werift's own `forceTurn`
behaviour. ICE settles on a `(relay, relay)` pair; the 5 MB sync
completes in ~3 s; the sentinel propagates; `inFlightSync` is
observable mid-run:

```
[result] SUCCESS — sentinel propagated via TURN relay in 3335ms; inFlightSync observed mid-run; candidate pair includes relay.
```

`transcript.json` next to the example records every getStats sample
taken during the run plus the public-surface `TransportSnapshot` from
both sides at the moment of the sentinel acquisition.

**pre-fix-emulated** — `POLLY_105_DISABLE_TURN_FIX=1` sets the new
`rtc.iceRelayEnforcement` option to `false`, reverting polly to the
pre-#105 behaviour of forwarding every gathered candidate up the
signalling channel regardless of policy. werift's `forceTurn` still
applies on its own check list, so the harness on same-machine
loopback ends up without a viable pair (relay candidates work, but
the leaked non-relay candidates pollute the check graph enough that
ICE cannot finalise) and the run exits 1:

```
[result] FAILURE — REASON: WebRTC peer-candidate never fired on at least one side (A.sawPeer=false B.sawPeer=false)
```

In a real-NAT topology — the shape the field issue is filed against —
the same falsification produces the more specific named failure the
ticket calls out: ICE finds a non-relay path that does not actually
carry data through the relay, so `candidatePairRelay` is false and
the report reads "negotiated candidate pair is not (relay, *)". The
named-failure ladder in `namedFailureReason` covers both shapes.

## Why this example is necessary (and why `mesh-large-initial-sync` cannot catch this)

`examples/mesh-large-initial-sync/main.ts` was issue #104's verification
artefact. It throttles werift's `RTCDataChannel.send` to simulate a
bandwidth-constrained transport. That simulation captures one
dimension of the failing shape (per-send delay) but bypasses every
other dimension a real TURN relay imposes — actual ICE candidate
gathering through `srflx` and `relay` types, DTLS over a real UDP
socket, SCTP fragmentation along the path MTU through coturn, and
per-message size limits enforced by the TURN allocation. Any of
those is a plausible site for the failure the field issue describes,
and the in-process bridge reaches none of them. This harness is the
relay-only variant: a real TURN server, real ICE candidate exchange,
real candidate-pair gating.

## Refusal gates (polly#105 item 3)

The example refuses to run with exit code `2` if any of the
following holds — each is a known false-positive surface for the
real-transport contract:

- `POLLY_105_TURN_MODE` is not `"real"`. The whole point of this
  harness is that in-process throttles miss the bug.
- `POLLY_105_ICE_TRANSPORT_POLICY` is not `"relay"`. Allowing host or
  srflx candidates would let ICE pick a direct loopback path on the
  same machine, never exercising TURN.
- The seeded snapshot is smaller than 1 MiB. Below that the
  fragmentation+reassembly path the bug lives in is not exercised.

These checks live in `refuseIfFalsePositiveConditions` near the top
of `main.ts` and run before the TURN subprocess boots.

## What changed in polly for #105

- **`rtc.iceTransportPolicy`** on `createMeshClient` — forwards to
  `MeshWebRTCAdapter` and into the constructor of every
  `RTCPeerConnection` the adapter builds. Default is the underlying
  implementation's own default; set to `"relay"` for relay-only.
- **`rtc.iceRelayEnforcement`** on `createMeshClient` (default `true`)
  — when the policy is `"relay"`, polly filters non-relay
  `a=candidate:` lines out of every outbound SDP description and
  drops non-relay candidates from the trickle stream. Mirrored on
  the receive side as a defence in depth. Setting to `false`
  reverts to pre-#105 behaviour for falsification only.
- **`TransportSnapshot`** type and **`refreshTransportStats()`** on
  `MeshClient`. Walks `RTCPeerConnection.getStats()` once per peer
  and persists the result onto the snapshot returned by
  `getPeerStateSnapshot()` — selected ICE candidate pair (local +
  remote candidate type, state, nominated flag, bytes), retransmission
  counters where the underlying stats expose them, and the most
  recent data-channel `onerror` message. Polly#105 item 7.

The polly#104 layer — 60 KiB fragment cap, send-side yield, and the
`inFlightSync` observability — is unchanged and still load-bearing.
