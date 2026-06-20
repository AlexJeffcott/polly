// The BDD reachability witness codegen (polly verify --witness). These pin the
// TS→TLA+ translation, the derived .cfg shape, and subsystem routing. The
// end-to-end check that a real TLC run reports reachable/unreachable lives in
// scripts/e2e-bdd-witness.ts (with a falsification gate).

import { describe, expect, test } from "bun:test";
import {
  bddPredicateToTLA,
  buildWitnessCfg,
  buildWitnessInvariant,
  buildWitnessModule,
  routeWitness,
  WITNESS_INVARIANT,
  WitnessTranslationError,
} from "../witness";

describe("bddPredicateToTLA", () => {
  test("flattens a boolean field and maps === to =", () => {
    expect(bddPredicateToTLA("user.loggedIn === true")).toBe(
      "contextStates[ctx].user_loggedIn = TRUE"
    );
  });

  test("maps false and !== to FALSE and #", () => {
    expect(bddPredicateToTLA("user.loggedIn !== false")).toBe(
      "contextStates[ctx].user_loggedIn # FALSE"
    );
  });

  test("keeps string literals and flattens nested fields", () => {
    expect(bddPredicateToTLA('user.role === "admin"')).toBe(
      'contextStates[ctx].user_role = "admin"'
    );
  });

  test("translates .length to Len() on the underlying sequence", () => {
    expect(bddPredicateToTLA("todos.length === 1")).toBe("Len(contextStates[ctx].todos) = 1");
  });

  test("conjoins multiple comparisons with TLA+ /\\", () => {
    expect(bddPredicateToTLA('user.loggedIn === true && user.role === "admin"')).toBe(
      'contextStates[ctx].user_loggedIn = TRUE /\\ contextStates[ctx].user_role = "admin"'
    );
  });

  test("does not mistake === for == when both could match", () => {
    // indexOf("==") would find the inner pair of "==="; the longest-first order
    // must split on === so the LHS/RHS are clean.
    expect(bddPredicateToTLA("todos.length >= 1")).toBe("Len(contextStates[ctx].todos) >= 1");
  });

  test("rejects a bare field with no comparison", () => {
    expect(() => bddPredicateToTLA("todos")).toThrow(WitnessTranslationError);
  });

  test("rejects an empty predicate", () => {
    expect(() => bddPredicateToTLA("   ")).toThrow(WitnessTranslationError);
  });
});

describe("buildWitnessInvariant / buildWitnessModule", () => {
  test("negates the predicate under an existential over Contexts", () => {
    expect(buildWitnessInvariant("contextStates[ctx].user_loggedIn = TRUE")).toBe(
      `${WITNESS_INVARIANT} == ~(\\E ctx \\in Contexts : contextStates[ctx].user_loggedIn = TRUE)`
    );
  });

  test("module EXTENDS the subsystem spec and declares the single invariant", () => {
    const mod = buildWitnessModule("Witness_auth_0", "UserApp_auth", "contextStates[ctx].x = TRUE");
    expect(mod).toContain("---- MODULE Witness_auth_0 ----");
    expect(mod).toContain("EXTENDS UserApp_auth");
    expect(mod).toContain(`${WITNESS_INVARIANT} ==`);
    expect(mod.trimEnd().endsWith("====")).toBe(true);
  });
});

describe("buildWitnessCfg", () => {
  const baseCfg = [
    "SPECIFICATION UserSpec",
    "",
    "\\* Constants",
    "CONSTANTS",
    "  Contexts = {background, content, popup}",
    "  NULL = NULL",
    "",
    "\\* Invariants to check",
    "INVARIANTS",
    "  TypeOK",
    "  UserStateTypeInvariant",
    "",
    "\\* Temporal properties to check",
    "PROPERTIES",
    "  EnsuresAfter_HandleUserLogin",
    "",
    "\\* State constraint",
    "CONSTRAINT",
    "  StateConstraint",
    "",
  ].join("\n");

  const cfg = buildWitnessCfg(baseCfg);

  test("keeps SPECIFICATION, CONSTANTS and CONSTRAINT verbatim", () => {
    expect(cfg).toContain("SPECIFICATION UserSpec");
    expect(cfg).toContain("  Contexts = {background, content, popup}");
    expect(cfg).toContain("  NULL = NULL");
    expect(cfg).toContain("CONSTRAINT\n  StateConstraint");
  });

  test("swaps the INVARIANTS list for the single witness", () => {
    expect(cfg).toContain(`INVARIANTS\n  ${WITNESS_INVARIANT}`);
    expect(cfg).not.toContain("TypeOK");
    expect(cfg).not.toContain("UserStateTypeInvariant");
  });

  test("drops PROPERTIES (the ensures temporal props play no part in reachability)", () => {
    expect(cfg).not.toContain("PROPERTIES");
    expect(cfg).not.toContain("EnsuresAfter_HandleUserLogin");
  });
});

describe("routeWitness", () => {
  const subsystems = {
    auth: { state: ["user.loggedIn", "user.role"] },
    todos: { state: ["todos"] },
    preferences: { state: ["theme"] },
  };

  test("routes a witness to the single subsystem owning all its fields", () => {
    expect(routeWitness(["user.loggedIn", "user.role"], subsystems)).toBe("auth");
    expect(routeWitness(["todos"], subsystems)).toBe("todos");
  });

  test("returns null when no subsystem owns the fields", () => {
    expect(routeWitness(["unknown.field"], subsystems)).toBeNull();
  });

  test("returns null for an empty field set", () => {
    expect(routeWitness([], subsystems)).toBeNull();
  });

  test("returns null when fields span more than one subsystem", () => {
    expect(routeWitness(["user.loggedIn", "todos"], subsystems)).toBeNull();
  });
});
