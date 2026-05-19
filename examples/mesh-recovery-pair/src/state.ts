// Verification-model state for polly#103.
//
// Each flag represents one observable in the wire-level race that
// main.ts reproduces against werift. Treating them as plain booleans
// loses information that does not change the property under check —
// the question is which steps have happened, not what their payloads
// were — and keeps TLC's state space small enough for the documented
// maxDepth ceiling.

import { $sharedState } from "@fairfox/polly/state";

// Signalling: has peer A's signalling roster reported peer B online?
// Set by ROSTER_PEER_JOINED.
export const aRosterHasB = $sharedState<boolean>("aRosterHasB", false);

// Keyring: does peer A's MeshKeyring contain peer B's signing key?
// Set by APPLY_PAIR_TOKEN.
export const aKeyringHasB = $sharedState<boolean>("aKeyringHasB", false);

// Adapter: does peer A's MeshWebRTCAdapter's captured knownPeers Set
// contain peer B? Pre-fix this was captured at construction and never
// refreshed; the polly#103 fix is to refresh it on keyring writes (and
// periodically). In this model the refresh happens synchronously inside
// APPLY_PAIR_TOKEN — that one line is the fix.
export const aAdapterKnowsB = $sharedState<boolean>("aAdapterKnowsB", false);

// Transport: is the data channel between A and B open? Requires both
// adapter awareness and roster presence.
export const dataChannelOpen = $sharedState<boolean>("dataChannelOpen", false);

// Sentinel: has peer A written the per-run sentinel into its
// $meshState document? Modelled as a single bit because the property
// under check is "B saw what A wrote," not the nonce identity.
export const sentinelWritten = $sharedState<boolean>("sentinelWritten", false);

// Sentinel observed on B's replica after sync traverses the mesh.
export const sentinelObserved = $sharedState<boolean>("sentinelObserved", false);
