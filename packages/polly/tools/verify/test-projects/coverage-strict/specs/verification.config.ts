// Verification config for the coverage-strict fixture (polly#160 Ask #1).
//
// Declares two state fields; the fixture's only handler writes `canSend`,
// leaving `authenticated` written by no modelled handler. Running
// `polly verify --strict` against this project fails closed at the
// model-coverage gate, before the TLC pass.

import { defineVerification } from "@fairfox/polly/verify";

export const verificationConfig = defineVerification({
  state: {
    "session.authenticated": { type: "boolean" },
    "session.canSend": { type: "boolean" },
  },

  messages: {
    maxInFlight: 1,
    maxTabs: 1,
  },
});
