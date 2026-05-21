/**
 * polly#114: the concurrent first-time $meshState seed guard.
 *
 * MeshSeed.tla model-checks the polly#113 race — two devices materialising
 * the same mesh document concurrently and forking it permanently. The
 * spec's `SeedDeterministic` constant is TRUE for the shipped fix; this
 * module rewrites it to FALSE when the fix is disabled, under which TLC
 * reports a `SeedConvergence` violation.
 *
 * The toggle is shared by the verify CLI (which honours the
 * `POLLY_113_DISABLE_FIX` environment variable, the same lever
 * seedDocumentBytes uses) and the e2e falsification script, so there is
 * one source of truth for how the guard is parameterised.
 */

/** The invariant whose violation is the polly#113 race. */
export const SEED_CONVERGENCE_INVARIANT = "SeedConvergence";

/**
 * Produce the MeshSeed.cfg contents for a run. With `disableFix` the
 * `SeedDeterministic` constant flips to FALSE — the pre-fix seed — and
 * TLC is expected to report a {@link SEED_CONVERGENCE_INVARIANT}
 * violation. Otherwise the committed cfg is used unchanged.
 */
export function meshSeedCfg(baseCfg: string, opts: { disableFix: boolean }): string {
  if (!opts.disableFix) return baseCfg;
  // Match the constant *declaration* line specifically: optional
  // indentation, then `SeedDeterministic = TRUE`, then end of line. A
  // plain string replace would hit the first occurrence — which is the
  // explanatory comment, not the declaration — and leave the real
  // constant untouched, silently defeating the falsification.
  const declaration = /^([ \t]*)SeedDeterministic = TRUE[ \t]*$/m;
  if (!declaration.test(baseCfg)) {
    throw new Error(
      "MeshSeed.cfg no longer declares `SeedDeterministic = TRUE` on its own line — the polly#114 seed-race guard cannot be falsified. Update tools/verify/src/runner/mesh-seed.ts."
    );
  }
  return baseCfg.replace(declaration, "$1SeedDeterministic = FALSE");
}

/** True when the polly#113 seed fix is disabled for this process. */
export function isSeedFixDisabled(env: NodeJS.ProcessEnv = process.env): boolean {
  return env["POLLY_113_DISABLE_FIX"] === "1";
}
