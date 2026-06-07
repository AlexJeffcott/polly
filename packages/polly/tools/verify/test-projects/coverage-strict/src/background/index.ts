// Verify fixture for polly#160 (Ask #1): a declared state field that NO handler
// writes. The config declares `session.authenticated` and `session.canSend`,
// but only `canSend` is ever assigned — `authenticated` has no modelled mutating
// path. `polly verify --strict` must fail closed on it.

import { createBackground } from "@fairfox/polly/background";
import { $sharedState } from "@fairfox/polly/state";

export const session = $sharedState("session", {
  authenticated: false,
  canSend: false,
});

const bus = createBackground();

// Writes canSend only. `authenticated` is declared but never assigned anywhere —
// the omission class the coverage report surfaces.
bus.on("OPEN_GATE", async () => {
  session.value.canSend = true;
  return { ok: true };
});

console.log("coverage-strict fixture loaded");
