// Verify fixture for polly#163: a capability granted by a NON-DISPATCHED path.
//
// Same capability as the capability-guard fixture (#160) — sends are gated
// behind `canSend`, which should only be true once `authenticated`. But here
// the offending write does not go through the message bus at all:
//
//  - AUTHENTICATE (dispatched): the correct path — sets `authenticated` AND
//    `canSend`. The extractor models it as a handler.
//  - RecoveryFlow.register (a plain method): grants `canSend` without
//    authenticating. It is not a `bus.on(...)` handler and is not an exported
//    top-level function, so the Issue #27 lift pass never reaches it. The model
//    has no transition for it; mutation testing has no oracle for it; and the
//    #162 coverage report cannot count it, because AUTHENTICATE already writes
//    `canSend` so the field is not "unwritten".
//
// polly#163's off-surface scan is the only layer that surfaces it: it reports
// `session.canSend` mutated in `RecoveryFlow.register` outside any modelled
// transition.

import { createBackground } from "@fairfox/polly/background";
import { $sharedState } from "@fairfox/polly/state";

export const session = $sharedState("session", {
  authenticated: false,
  canSend: false,
});

const bus = createBackground();

// Correct, dispatched path: authentication grants the capability and its
// precondition. Modelled as the AUTHENTICATE handler.
bus.on("AUTHENTICATE", async () => {
  session.value.authenticated = true;
  session.value.canSend = true;
  return { ok: true };
});

// The bug (polly#163): a recovery flow grants the capability from a plain
// method that never touches the bus. Off-surface — no modelled transition.
class RecoveryFlow {
  register() {
    session.value.canSend = true;
    // BUG: grants canSend without authenticating, via a non-dispatched path.
  }
}

const recovery = new RecoveryFlow();
recovery.register();

console.log("coverage-offsurface fixture loaded");
