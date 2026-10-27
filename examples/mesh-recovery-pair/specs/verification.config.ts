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

  // The chain is one context receiving five messages. Every extra context
  // multiplies the sources and target sets of each send.
  contexts: ["background"],

  messages: {
    // PEER_CANDIDATE and PEER_DISCONNECTED write no state; they would only
    // add interleavings.
    include: [
      "ROSTER_PEER_JOINED",
      "APPLY_PAIR_TOKEN",
      "OPEN_DATA_CHANNEL",
      "WRITE_SENTINEL",
      "RECEIVE_SENTINEL",
    ],
    // The message log never shrinks, so the five-message chain needs
    // maxInFlight 5. At 2, OPEN_DATA_CHANNEL through RECEIVE_SENTINEL were
    // never delivered and their ensures held vacuously.
    maxInFlight: 5,
    // One tab (Tabs = 0..maxTabs). No handler reads the tab; at maxTabs 1
    // each send doubled and the model did not finish.
    maxTabs: 0,

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
  },

  onBuild: "warn",
  onRelease: "error",
});
