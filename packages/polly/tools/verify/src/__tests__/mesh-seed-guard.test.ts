/**
 * polly#114: the mesh verify fixture and the polly#113 seed-race guard.
 *
 * Two concerns:
 *
 *  1. The `mesh-seed-guard` test-project exercises the polly#117 mesh
 *     codegen end-to-end — `analyzeCodebase` discovers its $meshState
 *     declarations and `generateTLA` emits the mesh model.
 *
 *  2. `meshSeedCfg` correctly toggles MeshSeed.cfg's SeedDeterministic
 *     constant — the lever that falsifies the guard. The full TLC runs
 *     (pass with the fix, fail without) live in
 *     scripts/e2e-verify-mesh-seed.ts; they need Docker, so they are an
 *     e2e script rather than a unit test.
 */

import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import path from "node:path";
import { analyzeCodebase } from "../../../analysis/src";
import { generateTLA } from "../codegen/tla";
import { isSeedFixDisabled, meshSeedCfg, SEED_CONVERGENCE_INVARIANT } from "../runner/mesh-seed";

// ─── The mesh-seed-guard fixture exercises the polly#117 mesh codegen ────────

describe("mesh-seed-guard fixture", () => {
  const projectPath = path.join(__dirname, "../../test-projects/mesh-seed-guard");

  // The fixture's verification.config.ts, inlined — generateTLA takes the
  // config object directly, and the CLI's config loader is not on this path.
  const config = {
    state: { "session.active": { type: "boolean" } },
    mesh: {
      "mesh-todos": { count: { type: "number", min: 0, max: 3 } },
      "mesh-presence": { online: { type: "boolean" } },
    },
    messages: { maxInFlight: 2, maxTabs: 1 },
    onBuild: "warn" as const,
    onRelease: "error" as const,
  };

  test("analyzeCodebase discovers both $meshState declarations", async () => {
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });

    const meshKeys = (analysis.meshOrPeerSignals ?? [])
      .filter((s) => s.kind === "mesh")
      .map((s) => s.key)
      .sort();
    expect(meshKeys).toEqual(["mesh-presence", "mesh-todos"]);
  });

  test("generateTLA emits the mesh model for the fixture", async () => {
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });
    const { spec } = await generateTLA(config, analysis);

    // polly#117 mesh codegen: the document set, the per-context replica
    // variable, and the sync action must all be present.
    expect(spec).toContain("MeshDocs ==");
    expect(spec).toContain('"mesh-todos"');
    expect(spec).toContain('"mesh-presence"');
    expect(spec).toContain("VARIABLE meshState");
    expect(spec).toContain("PropagateMeshOp");
  });
});

// ─── meshSeedCfg toggles the falsification constant ─────────────────────────

describe("meshSeedCfg", () => {
  const specDir = path.join(__dirname, "../../specs/tla");
  const baseCfg = readFileSync(path.join(specDir, "MeshSeed.cfg"), "utf8");

  test("the committed cfg ships with the fix in place", () => {
    expect(baseCfg).toMatch(/^[ \t]*SeedDeterministic = TRUE[ \t]*$/m);
  });

  test("disableFix=false returns the cfg unchanged", () => {
    expect(meshSeedCfg(baseCfg, { disableFix: false })).toBe(baseCfg);
  });

  test("disableFix=true flips the SeedDeterministic declaration to FALSE", () => {
    const flipped = meshSeedCfg(baseCfg, { disableFix: true });
    expect(flipped).toMatch(/^[ \t]*SeedDeterministic = FALSE[ \t]*$/m);
    expect(flipped).not.toMatch(/^[ \t]*SeedDeterministic = TRUE[ \t]*$/m);
  });

  test("flips the declaration, not a comment that mentions the constant", () => {
    // A plain string replace hits the first occurrence — here the
    // comment — and leaves the real constant untouched, silently
    // defeating the falsification. The declaration must be the one flipped.
    const cfg = [
      "\\* SeedDeterministic = TRUE models the polly#113 fix.",
      "CONSTANTS",
      "    Peers = {p1, p2}",
      "    SeedDeterministic = TRUE",
    ].join("\n");
    const flipped = meshSeedCfg(cfg, { disableFix: true });

    // The comment is untouched; the declaration is flipped.
    expect(flipped).toContain("\\* SeedDeterministic = TRUE models the polly#113 fix.");
    expect(flipped).toMatch(/^ {4}SeedDeterministic = FALSE$/m);
  });

  test("throws if the cfg no longer declares the constant", () => {
    expect(() => meshSeedCfg("CONSTANTS\n    Peers = {p1}", { disableFix: true })).toThrow(
      /SeedDeterministic/
    );
  });

  test("isSeedFixDisabled reads POLLY_113_DISABLE_FIX", () => {
    expect(isSeedFixDisabled({ POLLY_113_DISABLE_FIX: "1" })).toBe(true);
    expect(isSeedFixDisabled({ POLLY_113_DISABLE_FIX: "0" })).toBe(false);
    expect(isSeedFixDisabled({})).toBe(false);
  });

  test("the guard names the SeedConvergence invariant", () => {
    expect(SEED_CONVERGENCE_INVARIANT).toBe("SeedConvergence");
    expect(baseCfg).toContain(SEED_CONVERGENCE_INVARIANT);
  });
});
