// Wires the BDD tier into mutation testing. The engine mutates the example's
// own handlers and re-runs the Gherkin scenarios (`polly bdd run`, which exits
// non-zero on any failure) against each mutant. A mutant in a BDD-covered
// behaviour is killed; a survivor in an uncovered handler (e.g. SET_THEME,
// TODO_SET_LIMIT, GET_*) is the weak-coverage signal — the mechanical
// complement to `polly bdd check`'s negative-complement warning.
import { defineMutation } from "@fairfox/polly/mutate";

export default defineMutation({
  targets: ["src/background/handlers.ts"],
  runner: {
    kind: "command",
    argv: ["bun", "run", "bdd"],
  },
  concurrency: 4,
  // No `timeout`: the scenarios run in well under a second, so the default
  // (baseline × 2 + 3 s) fits.
});
