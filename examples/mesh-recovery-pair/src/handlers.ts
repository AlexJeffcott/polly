// Verification-model handlers for polly#103.
//
// Each handler corresponds to one wire-level event in the race that
// main.ts reproduces. The handlers form an ordered chain:
//
//   ROSTER_PEER_JOINED  → APPLY_PAIR_TOKEN  → OPEN_DATA_CHANNEL
//                       → WRITE_SENTINEL    → RECEIVE_SENTINEL
//
// The polly#103 contract is encoded as the ensures() on
// APPLY_PAIR_TOKEN: applying the pair token must leave the adapter
// knowing the peer. In the post-fix path that ensures holds because
// the same handler refreshes aAdapterKnowsB. Comment out the
// `aAdapterKnowsB.value = true` line below and re-run `polly verify`
// to see TLC produce the counterexample trace.

import { createBackground } from "@fairfox/polly/background";
import { ensures, requires } from "@fairfox/polly/verify";
import type { ExtensionMessage } from "@fairfox/polly/types";
import {
  aAdapterKnowsB,
  aKeyringHasB,
  aRosterHasB,
  dataChannelOpen,
  sentinelObserved,
  sentinelWritten,
} from "./state";

type MeshRecoveryMessages =
  | { type: "ROSTER_PEER_JOINED" }
  | { type: "APPLY_PAIR_TOKEN" }
  | { type: "OPEN_DATA_CHANNEL" }
  | { type: "WRITE_SENTINEL" }
  | { type: "RECEIVE_SENTINEL" };

type AllMessages = ExtensionMessage | MeshRecoveryMessages;

const bus = createBackground<AllMessages>();

// 1. Signalling tells peer A that peer B is online. This arrives
//    BEFORE the pair token in the real flow (the 250ms gap in
//    main.ts); the temporal constraint in verification.config.ts
//    encodes that ordering.
bus.on("ROSTER_PEER_JOINED", () => {
  aRosterHasB.value = true;
  ensures(aRosterHasB.value === true, "Roster must reflect peer-joined after the event fires");
  return { ok: true };
});

// 2. The pair token lands on peer A's keyring. In the post-fix path
//    this also refreshes the WebRTC adapter's captured knownPeers Set
//    — the line marked POLLY_103_FIX below. Pre-fix that line was
//    absent (the adapter's Set was only set at construction) and the
//    ensures fails.
bus.on("APPLY_PAIR_TOKEN", () => {
  requires(
    aRosterHasB.value === true,
    "Pair token in this scenario lands after the signalling roster reports the peer"
  );

  aKeyringHasB.value = true;
  // POLLY_103_FIX — comment this line out to reproduce the pre-fix bug.
  aAdapterKnowsB.value = true;

  ensures(aKeyringHasB.value === true, "Keyring must contain peer after pair token applied");
  ensures(
    aAdapterKnowsB.value === true,
    "polly#103: applying the pair token must refresh the adapter knownPeers"
  );
  return { ok: true };
});

// 3. With both sides aware of each other, the WebRTC data channel
//    can open. Modelled as a single event because the property under
//    check does not distinguish ICE / DTLS / DataChannel substates.
bus.on("OPEN_DATA_CHANNEL", () => {
  requires(
    aAdapterKnowsB.value === true,
    "Data channel can only open once the adapter knows the peer"
  );
  requires(
    aRosterHasB.value === true,
    "Data channel can only open once the roster confirms the peer"
  );

  dataChannelOpen.value = true;

  ensures(dataChannelOpen.value === true, "Data channel must be open after the open event");
  return { ok: true };
});

// 4. Peer A writes the sentinel into its $meshState document.
bus.on("WRITE_SENTINEL", () => {
  requires(dataChannelOpen.value === true, "Sentinel is written after the channel is open");

  sentinelWritten.value = true;

  ensures(sentinelWritten.value === true, "Sentinel write must register in shared state");
  return { ok: true };
});

// 5. Peer B's replica receives the sentinel via Automerge sync.
//    This is the load-bearing assertion in main.ts: "B's
//    $meshState.value changed in response."
bus.on("RECEIVE_SENTINEL", () => {
  requires(sentinelWritten.value === true, "B can only observe a sentinel that A actually wrote");
  requires(dataChannelOpen.value === true, "Receive can only happen across an open data channel");

  sentinelObserved.value = true;

  ensures(sentinelObserved.value === true, "Sentinel must be observed after receive");
  ensures(
    aKeyringHasB.value === true,
    "Convergence: a peer that observes A's write must be in A's keyring"
  );
  return { ok: true };
});
