// Verification config for the coverage-offsurface fixture (polly#163).
//
// Declares the same `session.authenticated` / `session.canSend` schema as the
// capability-guard fixture. The point of this fixture is NOT the capability
// invariant (the offending write is invisible to TLC — it is not a modelled
// transition) but the off-surface mutator scan: `polly verify` must report that
// `session.canSend` is mutated outside any modelled transition, and `--strict`
// must fail closed on it.

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
