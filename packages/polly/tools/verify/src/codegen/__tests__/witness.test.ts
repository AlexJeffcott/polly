// The BDD reachability witness codegen (polly verify --witness). These pin the
// TS→TLA+ translation, the derived .cfg shape, and subsystem routing. The
// end-to-end check that a real TLC run reports reachable/unreachable lives in
// scripts/e2e-bdd-witness.ts (with a falsification gate).

import { describe, expect, test } from "bun:test";
import {
  bareFieldRenderer,
  bddPredicateToTLA,
  buildWitnessCfg,
  buildWitnessInvariant,
  buildWitnessInvariantBare,
  buildWitnessModule,
  parseModuleName,
  routeWitness,
  WITNESS_INVARIANT,
  WitnessTranslationError,
  witnessPolarity,
  witnessSpecLocation,
  witnessVerdict,
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

describe("witnessPolarity / witnessVerdict", () => {
  test("the @forbidden tag flips polarity; everything else is positive", () => {
    expect(witnessPolarity(["forbidden"])).toBe("forbidden");
    expect(witnessPolarity(["negative", "forbidden"])).toBe("forbidden");
    expect(witnessPolarity([])).toBe("positive");
    expect(witnessPolarity(["formal"])).toBe("positive");
  });

  test("positive: reachable passes, unreachable fails (the scenario lies)", () => {
    expect(witnessVerdict("positive", true)).toMatchObject({ status: "reachable", ok: true });
    expect(witnessVerdict("positive", false)).toMatchObject({ status: "unreachable", ok: false });
  });

  test("forbidden: unreachable passes, reachable fails (the defect)", () => {
    expect(witnessVerdict("forbidden", false)).toMatchObject({ status: "excluded", ok: true });
    expect(witnessVerdict("forbidden", true)).toMatchObject({ status: "violated", ok: false });
  });

  test("the verdict is the exact dual across polarities", () => {
    for (const reachable of [true, false]) {
      expect(witnessVerdict("positive", reachable).ok).toBe(
        !witnessVerdict("forbidden", reachable).ok
      );
    }
  });
});

// Targeting a HAND-WRITTEN spec (customTLAPaths) instead of the generated one —
// the worked example is cochlea's VoiceTurn echo-safety: a forbidden state where
// the spec's own `Mic`/`Speaker` variables are both on.
describe("parseModuleName", () => {
  test("reads the module name from a MODULE header", () => {
    expect(parseModuleName("---- MODULE EdgeFold ----\nEXTENDS Naturals\n====")).toBe("EdgeFold");
  });

  test("tolerates varied dash runs and surrounding whitespace", () => {
    expect(parseModuleName("\n\n--------- MODULE VoiceTurn ---------\n")).toBe("VoiceTurn");
  });

  test("returns null when there is no MODULE header", () => {
    expect(parseModuleName("EXTENDS Naturals\nVARIABLES x\n")).toBeNull();
  });
});

describe("bareFieldRenderer / bddPredicateToTLA against a hand-written spec", () => {
  test("maps BDD field names to the spec's own variables (no contextStates)", () => {
    const render = bareFieldRenderer({ mic: "Mic", speaker: "Speaker" });
    expect(bddPredicateToTLA("mic === true && speaker === true", render)).toBe(
      "Mic = TRUE /\\ Speaker = TRUE"
    );
  });

  test("falls back to the flattened field name when unmapped", () => {
    expect(bddPredicateToTLA("door.open === false", bareFieldRenderer())).toBe("door_open = FALSE");
  });

  test("default renderer is unchanged (still reads contextStates[ctx])", () => {
    expect(bddPredicateToTLA("mic === true")).toBe("contextStates[ctx].mic = TRUE");
  });
});

describe("buildWitnessInvariantBare / buildWitnessModule({ bare })", () => {
  test("the bare invariant drops the Contexts existential", () => {
    expect(buildWitnessInvariantBare("Mic = TRUE /\\ Speaker = TRUE")).toBe(
      `${WITNESS_INVARIANT} == ~(Mic = TRUE /\\ Speaker = TRUE)`
    );
  });

  test("a bare module EXTENDS the hand-written spec and carries the bare invariant", () => {
    const mod = buildWitnessModule(
      "Witness_voice_0",
      "VoiceTurn",
      "Mic = TRUE /\\ Speaker = TRUE",
      {
        bare: true,
      }
    );
    expect(mod).toContain("---- MODULE Witness_voice_0 ----");
    expect(mod).toContain("EXTENDS VoiceTurn");
    expect(mod).toContain(`${WITNESS_INVARIANT} == ~(Mic = TRUE /\\ Speaker = TRUE)`);
    expect(mod).not.toContain("\\E ctx");
  });

  test("without { bare } the generated existential form is unchanged", () => {
    const mod = buildWitnessModule("Witness_auth_0", "UserApp_auth", "contextStates[ctx].x = TRUE");
    expect(mod).toContain("\\E ctx \\in Contexts");
  });
});

describe("witnessSpecLocation", () => {
  test("a custom binding resolves the hand-written spec, its dir, and module", () => {
    const loc = witnessSpecLocation(
      "/repo",
      "voice",
      { tla: "specs/VoiceTurn.tla", cfg: "specs/VoiceTurn_safe.cfg" },
      "VoiceTurn"
    );
    expect(loc).toMatchObject({
      dir: "/repo/specs",
      tlaPath: "/repo/specs/VoiceTurn.tla",
      cfgPath: "/repo/specs/VoiceTurn_safe.cfg",
      module: "VoiceTurn",
      custom: true,
    });
  });

  test("no custom binding falls back to the generated UserApp_<subsystem> path", () => {
    const loc = witnessSpecLocation("/repo", "auth", undefined, "");
    expect(loc).toMatchObject({
      dir: "/repo/specs/tla/generated/auth",
      tlaPath: "/repo/specs/tla/generated/auth/UserApp_auth.tla",
      cfgPath: "/repo/specs/tla/generated/auth/UserApp_auth.cfg",
      module: "UserApp_auth",
      custom: false,
    });
  });
});

describe("buildWitnessCfg against a hand-written cfg", () => {
  test("carries INIT/NEXT when the cfg names them instead of SPECIFICATION", () => {
    const baseCfg = ["INIT Init", "NEXT Next", "", "INVARIANT EchoSafety", ""].join("\n");
    const cfg = buildWitnessCfg(baseCfg);
    expect(cfg).toContain("INIT Init");
    expect(cfg).toContain("NEXT Next");
    expect(cfg).toContain(`INVARIANTS\n  ${WITNESS_INVARIANT}`);
    expect(cfg).not.toContain("EchoSafety");
  });

  // Regression: a hand-written cfg binds its constant with the singular `CONSTANT`
  // keyword inline (the form TLC docs use, and what cochlea's VoiceTurn_safe.cfg
  // writes). A plain CONSTANTS-section read dropped it, so TLC failed with "the
  // constant parameter Controller is not assigned a value".
  test("captures a singular inline CONSTANT (the hand-written VoiceTurn form)", () => {
    const baseCfg = [
      "SPECIFICATION Spec",
      'CONSTANT Controller = "safe"',
      "INVARIANT TypeOK",
      "INVARIANT EchoSafe",
      "",
    ].join("\n");
    const cfg = buildWitnessCfg(baseCfg);
    expect(cfg).toContain("SPECIFICATION Spec");
    expect(cfg).toContain('CONSTANTS\n  Controller = "safe"');
    expect(cfg).toContain(`INVARIANTS\n  ${WITNESS_INVARIANT}`);
    expect(cfg).not.toContain("EchoSafe");
  });

  test("captures a singular CONSTANT given as an indented section", () => {
    const baseCfg = ["SPECIFICATION Spec", "CONSTANT", '  Controller = "safe"', ""].join("\n");
    expect(buildWitnessCfg(baseCfg)).toContain('CONSTANTS\n  Controller = "safe"');
  });

  test("still captures the plural CONSTANTS section (no regression)", () => {
    const baseCfg = ["SPECIFICATION Spec", "CONSTANTS", "  N = 3", "  M = 2", ""].join("\n");
    const cfg = buildWitnessCfg(baseCfg);
    expect(cfg).toContain("  N = 3");
    expect(cfg).toContain("  M = 2");
  });
});
