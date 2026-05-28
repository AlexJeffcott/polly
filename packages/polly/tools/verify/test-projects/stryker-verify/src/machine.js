// Fixture for the polly#143 Stryker-ignorer e2e (scripts/e2e-stryker-verify.ts).
//
// `requires` / `ensures` are declared here as local no-ops so the file is
// self-contained: the e2e never executes it (the test runner is `exit 0`),
// Stryker only instruments it statically. The point is the *shape* — string
// literals and comparison operators sitting inside verify callsites, exactly
// the survivors reported in the issue — next to real production logic that
// must still be mutated.

const requires = (condition, _message) => void condition;
const ensures = (condition, _message) => void condition;

export function transition(state, label) {
  requires(state === "idle", "pre: must start idle");
  const next = label === "go" ? "running" : "idle";
  ensures(next === "running" || next === "idle", "post: settled");
  return next;
}
