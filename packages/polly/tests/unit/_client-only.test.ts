/**
 * Phase 1 prototype test for plan risk #4: server-side exclusion mechanism.
 *
 * Verifies that a module marked as client-only throws a structured error at
 * import time when evaluated in a server-side runtime (Bun, Node), and that
 * the error message names the file and the plan risk so future debugging is
 * easy. Bun's bun:test environment has no `window`, so the client-only guard
 * fires.
 *
 * The bypass mechanism for test environments — set `globalThis.window` to
 * any object before importing the module — is documented in the source file
 * itself rather than tested here. ESM module evaluation is cached at the
 * first attempt, so we cannot demonstrate both the throwing and the
 * non-throwing path in one file without per-import cache busting that
 * TypeScript's static module resolution does not understand.
 */

import { describe, expect, test } from "bun:test";

describe("client-only exclusion prototype", () => {
  test("importing the client-only module from a server-side runtime throws", async () => {
    let caught: unknown;
    try {
      await import("@/shared/lib/_client-only");
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(Error);
    const message = (caught as unknown as Error).message;
    expect(message).toMatch(/client-only/i);
    expect(message).toMatch(/_client-only\.ts/);
    expect(message).toMatch(/plan risk #4/);
  });
});
