// extractWitnesses reduces each scenario to the Then-predicate the verify
// witness checks for reachability. These pin the reduction: value substitution
// into stateExpr placeholders, the conjunction of comparison Thens, and the
// honest skipping of bare-field / runtime-only Thens. The end-to-end TLC check
// lives in scripts/e2e-bdd-witness.ts.

import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import type { ScenarioWitness } from "../witness";
import { extractWitnesses } from "../witness";

const stepsSource = resolve(import.meta.dir, "../steps.ts");

// A self-contained feature exercising every reduction branch.
const FEATURE = `Feature: Sessions
  Scenario: Sign in as admin
    When the user signs in
    Then the user is signed in
    And their role is "admin"

  Scenario: A runtime-only outcome is not witnessable
    When something happens
    Then the change is refused

  Scenario: A bare-field outcome is not witnessable
    When a todo is added
    Then the list is non-empty
`;

const STEPS = `
import { defineStep } from ${JSON.stringify(stepsSource)};

defineStep({ pattern: "the user signs in", when: () => {}, message: "USER_LOGIN" });
defineStep({ pattern: "something happens", when: () => {}, message: "NOOP" });
defineStep({ pattern: "a todo is added", when: () => {}, message: "TODO_ADD" });

defineStep({ pattern: "the user is signed in", then: () => {}, stateExpr: "user.loggedIn === true" });
defineStep({ pattern: "their role is {string}", then: () => {}, stateExpr: 'user.role === "{0}"' });
// No stateExpr — a runtime-only assertion (e.g. a response check).
defineStep({ pattern: "the change is refused", then: () => {} });
// A bare field reference — names a field but asserts no comparison.
defineStep({ pattern: "the list is non-empty", then: () => {}, stateExpr: "todos" });
`;

let dir: string;
let witnesses: ScenarioWitness[];

beforeAll(async () => {
  dir = mkdtempSync(join(tmpdir(), "polly-witness-extract-"));
  const featureFile = join(dir, "sessions.feature");
  const stepsFile = join(dir, "sessions.steps.ts");
  writeFileSync(featureFile, FEATURE);
  writeFileSync(stepsFile, STEPS);
  witnesses = await extractWitnesses([featureFile], [stepsFile]);
});

afterAll(() => {
  rmSync(dir, { recursive: true, force: true });
});

describe("extractWitnesses", () => {
  test("substitutes captured args and conjoins comparison Thens", () => {
    const w = witnesses.find((x) => x.scenario === "Sign in as admin");
    expect(w?.predicate).toBe('user.loggedIn === true && user.role === "admin"');
    expect(w?.fields).toEqual(["user.loggedIn", "user.role"]);
    expect(w?.skipped).toEqual([]);
  });

  test("a runtime-only Then (no stateExpr) yields no predicate and is recorded as skipped", () => {
    const w = witnesses.find((x) => x.scenario === "A runtime-only outcome is not witnessable");
    expect(w?.predicate).toBeNull();
    expect(w?.skipped).toContain("the change is refused");
  });

  test("a bare-field Then (no comparison) is not witnessable", () => {
    const w = witnesses.find((x) => x.scenario === "A bare-field outcome is not witnessable");
    expect(w?.predicate).toBeNull();
    expect(w?.skipped).toContain("the list is non-empty");
    expect(w?.fields).toEqual([]);
  });
});
