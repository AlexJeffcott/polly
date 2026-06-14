/**
 * The convergence pollers accept an optional `context()` that is evaluated
 * only on timeout and appended to the failure, so a hung e2e self-diagnoses
 * with live transport state instead of leaving the reader to guess. These
 * tests pin that contract: the context appears on timeout, never on success,
 * and a broken context can never mask the real timeout.
 */

import { describe, expect, test } from "bun:test";
import {
  type RelayConvergenceTarget,
  waitForRelayConvergence,
} from "../../tools/test/src/e2e-relay/wait-for-relay-convergence";
import { resolveContext } from "../../tools/test/src/e2e-shared/timeout-context";

describe("resolveContext", () => {
  test("returns empty string when no context is supplied", async () => {
    expect(await resolveContext(undefined)).toBe("");
  });

  test("formats a transport line under the failure", async () => {
    expect(await resolveContext(() => "clients=2 docs=1")).toBe("\n\ntransport: clients=2 docs=1");
  });

  test("awaits an async context", async () => {
    expect(await resolveContext(async () => "clients=3 docs=0")).toBe(
      "\n\ntransport: clients=3 docs=0"
    );
  });

  test("swallows a throwing context so it cannot mask the timeout", async () => {
    const out = await resolveContext(() => {
      throw new Error("boom");
    });
    expect(out).toContain("context threw: boom");
  });
});

describe("waitForRelayConvergence — timeout context", () => {
  const stuck: RelayConvergenceTarget[] = [{ peerId: "peer-1", read: () => "never" }];

  test("appends the context snapshot on timeout", async () => {
    const err = await waitForRelayConvergence(stuck, (v) => v === "done", {
      timeoutMs: 30,
      pollMs: 5,
      context: () => "clients=0 docs=0",
    }).catch((e: unknown) => e);

    expect(err).toBeInstanceOf(Error);
    if (!(err instanceof Error)) throw new Error("expected an Error");
    const message = err.message;
    expect(message).toContain("did not hold for every peer");
    expect(message).toContain("peer-1");
    expect(message).toContain("transport: clients=0 docs=0");
  });

  test("omits the transport line when no context is supplied", async () => {
    const err = await waitForRelayConvergence(stuck, (v) => v === "done", {
      timeoutMs: 30,
      pollMs: 5,
    }).catch((e: unknown) => e);

    expect(err).toBeInstanceOf(Error);
    if (!(err instanceof Error)) throw new Error("expected an Error");
    expect(err.message).not.toContain("transport:");
  });

  test("never evaluates the context when the predicate already holds", async () => {
    let evaluated = false;
    const ready: RelayConvergenceTarget[] = [{ peerId: "peer-1", read: () => "done" }];
    await waitForRelayConvergence(ready, (v) => v === "done", {
      context: () => {
        evaluated = true;
        return "should-not-run";
      },
    });
    expect(evaluated).toBe(false);
  });
});
