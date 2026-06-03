// Verification config for the capability-guard fixture (polly#160).
//
// `capabilities` declares the directional invariant `canSend => authenticated`
// (a send capability requires an authenticated session). It desugars to a TLA+
// safety invariant TLC checks at every reachable state — catching the REGISTER
// path that grants canSend without authenticating.
//
// `coupledFields` additionally lints, statically, any handler that writes one
// of the pair without the other.

import { defineVerification } from "@fairfox/polly/verify";

export const verificationConfig = defineVerification({
  state: {
    "session.authenticated": { type: "boolean" },
    "session.canSend": { type: "boolean" },
  },

  // polly#160: the sound, whole-reachable-state detector.
  capabilities: [
    {
      name: "canSend",
      enabledBy: "session.value.canSend",
      requires: "session.value.authenticated",
      message: "sends require an authenticated session",
    },
  ],

  // polly#160: the fast, per-handler static lint.
  coupledFields: [["session.authenticated", "session.canSend"]],

  messages: {
    maxInFlight: 1,
    maxTabs: 1,
  },
});
