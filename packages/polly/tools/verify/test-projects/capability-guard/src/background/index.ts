// Verify fixture for polly#160: a capability granted without its precondition.
//
// The app gates sends behind `canSend`, which should only be true once the
// connection is `authenticated`. Two handlers establish a session:
//
//  - AUTHENTICATE: the correct path — sets `authenticated` AND `canSend`.
//  - REGISTER: the bug — a new-user recovery path that grants `canSend`
//    but forgets to mark the session `authenticated`.
//
// The config declares the capability `canSend => authenticated`. TLC reaches
// the post-REGISTER state (canSend = true, authenticated = false) and reports
// the invariant violation with a counterexample. The coupledFields lint flags
// REGISTER statically, as a fast hint.

import { createBackground } from "@fairfox/polly/background";
import { $sharedState } from "@fairfox/polly/state";

export const session = $sharedState("session", {
  authenticated: false,
  canSend: false,
});

const bus = createBackground();

// Correct path: authentication grants the capability and its precondition.
bus.on("AUTHENTICATE", async () => {
  session.value.authenticated = true;
  session.value.canSend = true;
  return { ok: true };
});

// The bug (polly#160): registration recovery grants the capability without
// establishing its precondition.
bus.on("REGISTER", async () => {
  session.value.canSend = true;
  // BUG: forgot `session.value.authenticated = true`.
  return { ok: true };
});

console.log("capability-guard fixture loaded");
