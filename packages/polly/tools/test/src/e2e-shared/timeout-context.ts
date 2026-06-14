/**
 * @fairfox/polly/test/e2e-shared — timeout diagnostic context.
 *
 * A convergence poller that times out can only show the per-peer values it
 * was watching. That answers "what did each peer see" but not "why" — was the
 * peer ever connected to the relay, does the hub even know about the document?
 * The pollers accept an optional `context()` that a caller wires to live
 * transport state (e.g. `relayStats(server)`); it is evaluated ONLY on the
 * timeout path and appended to the failure, so a hung e2e self-diagnoses
 * instead of leaving the reader to guess.
 *
 * Borrowed from fairfox's `waitForLine(..., context)` pattern, where the relay
 * heartbeat is embedded in every timeout so the error pinpoints sync state.
 */

/** Evaluate a timeout-only diagnostic context, never letting it throw — a
 *  broken context must not mask the real timeout it is trying to explain. */
export async function resolveContext(
  context: (() => string | Promise<string>) | undefined
): Promise<string> {
  if (!context) return "";
  try {
    return `\n\ntransport: ${await context()}`;
  } catch (err) {
    return `\n\ntransport: <context threw: ${err instanceof Error ? err.message : String(err)}>`;
  }
}
