#!/usr/bin/env bun
/**
 * Subprocess entry for a single "module" case.
 *
 * Spawned by the engine as `bun worker.ts <modulePath> <id>`. Running each case
 * in its own process is deliberate: the e2e scripts mutate globals (happy-dom),
 * bind ephemeral ports, and drive Puppeteer — they were written assuming
 * process isolation, and the engine preserves it.
 *
 * Protocol: the worker prints exactly one sentinel line
 *   __TIER_RESULT__{"pass":true,...}
 * to stdout. Everything else on stdout is the case's own logging, forwarded by
 * the parent. If the case hard-exits (legacy `process.exit(1)`) before the
 * sentinel, the parent falls back to the worker's exit code.
 */
import { standaloneContext, type TierResult } from "../e2e-shared/contract";
import { SENTINEL } from "./protocol";

function emit(result: TierResult): void {
  process.stdout.write(`\n${SENTINEL}${JSON.stringify(result)}\n`);
}

async function runWorker(): Promise<void> {
  const modulePath = process.argv[2];
  if (!modulePath) {
    emit({ pass: false, message: "worker: no module path given" });
    return;
  }

  try {
    // Importing a converted script is side-effect-free (its self-run footer is
    // guarded by import.meta.main). Importing a legacy script runs its top-level
    // main() now, which sets process.exitCode.
    const mod: { run?: (ctx: unknown) => Promise<TierResult> } = await import(modulePath);

    if (typeof mod.run === "function") {
      const result = await mod.run(standaloneContext());
      emit({ pass: Boolean(result?.pass), message: result?.message, detail: result?.detail });
    } else {
      // Legacy: the import side-effect already ran the test; trust its exit code.
      emit({ pass: (process.exitCode ?? 0) === 0 });
    }
  } catch (err) {
    emit({ pass: false, message: err instanceof Error ? err.message : String(err) });
  }
}

// Only execute when invoked directly; the engine also imports SENTINEL from here.
if (import.meta.main) {
  await runWorker();
  // Force exit so an open Puppeteer/server handle can't keep the worker alive;
  // the result has already been emitted and captured by the parent.
  process.exit(0);
}
