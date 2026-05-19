/**
 * @fairfox/polly/test/e2e-mesh — assertions over the mesh-diagnostics
 * stream.
 *
 * Every e2e script that drives the mesh subscribes to the diagnostic
 * stream before it starts and runs the assertions in `assertNoSilentDrops`
 * before exiting. The default is "no unexpected diagnostics fired"; a
 * script that legitimately exercises a drop branch (e.g. a revocation
 * test) supplies an allowlist of expected kinds so the gate stays loud
 * about everything else.
 *
 * This is the test-kit half of the diagnostic-obligation move: the lint
 * half (forbidding new silent-drop branches that do not emit) lands
 * separately as `scripts/check-mesh-diagnostics.ts`.
 */

import {
  type MeshDiagnostic,
  type MeshDiagnosticEvent,
  recordMeshDiagnostics,
} from "../../../../src/shared/lib/mesh-diagnostics";

export interface MeshAssertionFailure extends Error {
  readonly kind: "mesh-assertion-failure";
  readonly unexpected: ReadonlyArray<MeshDiagnosticEvent>;
}

export class MeshAssertionError extends Error implements MeshAssertionFailure {
  readonly kind = "mesh-assertion-failure";
  readonly unexpected: ReadonlyArray<MeshDiagnosticEvent>;
  constructor(message: string, unexpected: ReadonlyArray<MeshDiagnosticEvent>) {
    super(message);
    this.name = "MeshAssertionError";
    this.unexpected = unexpected;
  }
}

export interface DiagnosticRecorder {
  /** Live capture buffer — reads see new events the moment they fire. */
  events: ReadonlyArray<MeshDiagnosticEvent>;
  /** Stop subscribing. Idempotent. */
  stop: () => void;
  /**
   * Run the no-silent-drops assertion against the captured buffer.
   * Throws {@link MeshAssertionError} if any unexpected diagnostic fired.
   * Pass `allow` with the kinds the script legitimately expected — the
   * gate fails on anything else.
   */
  assertNoSilentDrops: (allow?: ReadonlyArray<MeshDiagnostic["kind"]>) => void;
}

/**
 * Begin capturing diagnostics for the duration of a script.
 *
 * @example
 * ```typescript
 * const diag = startDiagnosticRecorder();
 * try {
 *   await driveTheScenario();
 *   diag.assertNoSilentDrops();
 * } finally {
 *   diag.stop();
 * }
 * ```
 */
export function startDiagnosticRecorder(): DiagnosticRecorder {
  const { events, stop } = recordMeshDiagnostics();

  function assertNoSilentDrops(allow: ReadonlyArray<MeshDiagnostic["kind"]> = []): void {
    const allowed = new Set(allow);
    const unexpected = events.filter(
      (event) => event.kind.startsWith("drop:") && !allowed.has(event.kind)
    );
    if (unexpected.length === 0) return;
    const summary = unexpected
      .map((event) => `  ${event.kind} ${JSON.stringify(eventDetails(event))}`)
      .join("\n");
    throw new MeshAssertionError(
      `Unexpected silent-drop diagnostics fired during the e2e run.\n${summary}\n` +
        `If a drop kind is legitimately expected for this scenario, pass it ` +
        `to assertNoSilentDrops({ allow: [...] }).`,
      unexpected
    );
  }

  return { events, stop, assertNoSilentDrops };
}

function eventDetails(event: MeshDiagnosticEvent): Record<string, unknown> {
  // Strip kind + timestamp; keep the rest as context.
  const { kind: _kind, timestamp: _ts, ...rest } = event;
  return rest;
}
