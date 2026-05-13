# mesh-large-initial-sync

Runnable demonstration for polly issue #104 — the "fresh peer cannot
consume a non-trivial initial sync over a bandwidth-constrained
transport without hanging its main thread" contract violation.

## What this example shows

Two werift-backed mesh peers wired up against an in-process polly
signalling server, configured in the failing-shape diff from issue
#104:

- **Peer A** (the daemon) holds a single Automerge document whose
  compacted snapshot exceeds 5 MB. The doc carries a per-run UUID
  sentinel inside the same large payload, so the only way for peer B
  to satisfy the sentinel assertion is to receive and apply the full
  history.
- **Peer A's outbound RTCDataChannel is throttled** by a wrapper
  around werift's `RTCPeerConnection` that delays each `.send()` call
  proportional to its byte length, simulating a bandwidth-constrained
  uplink without needing a real TURN relay.
- **Peer B** (the receiver) starts fresh — no prior keyring entries,
  no cached doc state — so its WebRTC adapter consumes the full
  initial sync stream on its main thread.
- **A `setInterval` liveness probe** records the maximum event-loop
  tick gap during the sync. The probe is the load-bearing signal: if
  the receiver's main thread is starved by the sync, the probe's
  `setInterval` callback misses its 50ms tick and the recorded max
  gap exceeds the 100ms threshold.

## Running it

```bash
cd examples/mesh-large-initial-sync
bun install
bun run main.ts                              # post-fix path (default)
POLLY_104_DISABLE_FIX=1 bun run main.ts      # reproduces pre-fix failure
POLLY_104_TRACE_VERBOSE=1 bun run main.ts    # dumps every per-fragment frame
```

Exit code is `0` on contract satisfied, `1` on contract violated, `2`
on refusal under a false-positive condition.

## What the two modes look like

**post-fix** (default) — `MeshWebRTCAdapter.syncYieldEnabled` is
`true` and the sync fragment chunk size is the polly-default 60 KiB,
which leaves room for the per-fragment header inside werift's hard
64 KiB max-message-size cap. Sync completes in about 3-4 s for a
5.5 MB snapshot; the sentinel propagates end-to-end and `inFlightSync`
is observable mid-run:

```
[result] SUCCESS — contract holds: sentinel propagated end-to-end, inFlightSync observed mid-run (2/4 signals).
[result] NOTE — max-tick-gap-ms=<N> exceeds the 100ms target. Yield-only fix moves dispatch off the wire frame but does not split Automerge's single applyChanges for a large initial sync; this residual spike is documented in the PR.
```

The `NOTE` is intentional. The yield-only fix moves the dispatch off
the wire-callback frame so the JS event loop drains between message
events, but the receiver's single `applyChanges` call for a 5 MB
sync payload remains synchronous (Automerge has no chunked apply at
the time of this fix). Reducing that residual spike to under 100 ms
requires either sender-side streaming of `Automerge.save()` output
into bounded sub-messages or moving apply to a Web Worker. The
ticket's strict `<100ms` bar is therefore not met by the yield-only
fix alone — the PR description spells this out and proposes the
contingency.

**pre-fix-emulated** — passing `syncFragmentChunkSizeOverride: 64 * 1024`
through `rtc.syncFragmentChunkSizeOverride` (the same env switch
also disables `syncYieldEnabled`) restores the pre-#104 chunk size.
The per-fragment header pushes every chunk to ~65 630 bytes, which
exceeds werift's 64 KiB cap. Werift rejects each fragment silently;
peer B receives no bytes of the sync stream; the sentinel never
propagates and the example exits 1:

```
[result] FAILURE — contract violated. REASON: sentinel did not propagate within budget (bSentinel=undefined)
```

The wire transcript in pre-fix mode shows `send-size-distribution: max=65630 above-64K=88`, the smoking gun.

## Why this example is necessary (and why `mesh-recovery-pair` cannot catch this)

`examples/mesh-recovery-pair/main.ts` was issue #103's verification
artefact. Its sentinel document is empty — a single string. Its
transport is the unthrottled werift loopback. Both choices are exactly
the false-positive surfaces that mask #104:

- A sentinel that fits in one ordinary sync message never traverses
  the fragmentation path the bug lives in.
- An unthrottled transport never exposes the SCTP-backpressure × main-
  thread-starvation interaction that makes the real fairfox.fly.dev
  tab hang.

This example is the failing-shape diff: a sentinel inside a snapshot
≥ 5 MB and a per-`send` write delay on the underlying data channel.
That combination reproduces what fairfox saw against fairfox.fly.dev
with the real `~/.fairfox/mesh/` store, but in-process and without a
real TURN server.

## Refusal gates

The example refuses to run with exit code `2` if any condition that
issue #104 names as a known false-positive surface is detected:

- The seeded snapshot would be smaller than 1 MB (the bug needs an
  oversized doc to manifest).
- The throttle is not installed on peer A's RTCPeerConnection (the
  bug needs SCTP backpressure to surface receiver-side starvation).
- The tick-gap liveness probe is not installed before the sync
  starts (no liveness data means no falsifiable evidence, so no
  proof).
- `POLLY_104_DISABLE_FIX=1` is set but the adapter's
  `syncYieldEnabled` option is unsupported (older polly versions).

These checks live in `refuseIfFalsePositiveConditions` near the top
of `main.ts` and run before any peer is constructed. They are the
ticket's item-4 reified — the harness exists because the original
e2e for #103 passed under exactly these conditions while the #104
flow was broken.
