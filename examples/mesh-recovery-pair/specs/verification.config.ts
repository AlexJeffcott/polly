// Verification configuration for the polly#103 race.
//
// The model in src/ encodes the wire-level race main.ts reproduces
// against werift as an ordered chain of polly handlers. This file
// bounds the state space TLC explores and pins the temporal ordering
// that reflects the 250ms gap in main.ts between the signalling
// roster reporting peer B and the pair token landing on peer A.

import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: verification configs use default export by convention
export default defineVerification({
  state: {
    aRosterHasB: { type: "boolean" },
    aKeyringHasB: { type: "boolean" },
    aAdapterKnowsB: { type: "boolean" },
    dataChannelOpen: { type: "boolean" },
    sentinelWritten: { type: "boolean" },
    sentinelObserved: { type: "boolean" },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,

    perMessageBounds: {
      ROSTER_PEER_JOINED: 1,
      APPLY_PAIR_TOKEN: 1,
      OPEN_DATA_CHANNEL: 1,
      WRITE_SENTINEL: 1,
      RECEIVE_SENTINEL: 1,
    },
  },

  tier2: {
    temporalConstraints: [
      {
        before: "ROSTER_PEER_JOINED",
        after: "APPLY_PAIR_TOKEN",
        description:
          "The signalling roster reports peer B before the pair token lands on peer A — the 250ms gap in main.ts",
      },
      {
        before: "APPLY_PAIR_TOKEN",
        after: "OPEN_DATA_CHANNEL",
        description: "The data channel can only open after pairing completes on the daemon side",
      },
      {
        before: "OPEN_DATA_CHANNEL",
        after: "WRITE_SENTINEL",
        description:
          "The sentinel is written into peer A's $meshState after the channel reports open",
      },
      {
        before: "WRITE_SENTINEL",
        after: "RECEIVE_SENTINEL",
        description: "Peer B observes the sentinel only after peer A writes it",
      },
    ],

    // Per CLAUDE.md and the audit on issue #75, maxInFlight=2 with
    // deliveredTo observable multiplies distinct states by |targets|
    // per delivered message. Depth 4 fits the documented state-pool
    // budget; the chain has five steps but the ordering constraints
    // collapse most of the search.
    boundedExploration: {
      maxDepth: 4,
    },
  },

  onBuild: "warn",
  onRelease: "error",
});
