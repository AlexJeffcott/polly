/**
 * The runner's contract drain: a step whose handler swallowed a
 * ContractViolation (the bus returns `{ success: false }` instead of
 * throwing) still fails, with the violation's message, because the primitives
 * recorded it on globalThis before throwing. A step that records nothing
 * passes, and the list is empty afterwards.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { runFeatures } from "../run.ts";
import type { RunResult } from "../types.ts";

const stepsSource = resolve(import.meta.dir, "../steps.ts");
const KEY = "__pollyContractViolations";
const MARKER = "[polly-contract ensures /abs/handlers.ts:9] role is set";

const FEATURE = `Feature: Drain
  Scenario: A swallowed violation fails the step that caused it
    When a handler swallows a violation
    Then the step is checked

  Scenario: A clean step passes
    When nothing is recorded
    Then the step is checked
`;

const STEPS = `
import { defineStep, defineWorld } from ${JSON.stringify(stepsSource)};

defineWorld({
  create: () => ({ bus: { send: async () => undefined }, signals: {}, vars: {} }),
  reset: () => {},
});
defineStep({
  pattern: "a handler swallows a violation",
  when: () => {
    (globalThis[${JSON.stringify(KEY)}] ??= []).push(new Error(${JSON.stringify(MARKER)}));
  },
});
defineStep({ pattern: "nothing is recorded", when: () => {} });
defineStep({ pattern: "the step is checked", then: () => {} });
`;

let dir: string;
let result: RunResult;

beforeAll(async () => {
  dir = mkdtempSync(join(tmpdir(), "polly-bdd-drain-"));
  const featureFile = join(dir, "drain.feature");
  const stepsFile = join(dir, "drain.steps.ts");
  writeFileSync(featureFile, FEATURE);
  writeFileSync(stepsFile, STEPS);
  result = await runFeatures({ featureFiles: [featureFile], stepFiles: [stepsFile] });
});

afterAll(() => {
  Reflect.deleteProperty(globalThis, KEY);
  rmSync(dir, { recursive: true, force: true });
});

describe("contract drain", () => {
  test("the step that left a violation fails with its message; the rest is skipped", () => {
    const [swallowed] = result.scenarios;
    expect(swallowed?.outcome).toBe("fail");
    expect(swallowed?.steps.map((s) => s.outcome)).toEqual(["fail", "skipped"]);
    expect(swallowed?.steps[0]?.message).toBe(MARKER);
  });

  test("a step that records nothing passes, and the list is drained", () => {
    expect(result.scenarios[1]?.outcome).toBe("pass");
    expect(result.failed).toBe(1);
    expect(Reflect.get(globalThis, KEY)).toEqual([]);
  });
});
