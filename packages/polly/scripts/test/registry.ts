/**
 * Polly's own tiered test plan.
 *
 * This file lives in scripts/ — not tools/ — on purpose: the repo's module
 * boundary forbids tools/ importing scripts/, and this registry references the
 * e2e scripts under scripts/. It is one of two front-ends over the reusable
 * engine in tools/test/src/tiers (the other being consumer auto-discovery
 * behind `polly test`).
 *
 * Tier order is fast → realistic → heavy. `--all` runs through e2e-mesh;
 * `--full` adds the Docker/mutation `verify` and the `static` gate.
 */
import type { CaseSpec, Tier, TierPlan } from "../../tools/test/src/tiers";

const scriptsDir = `${import.meta.dir}/..`;
const packageRoot = `${import.meta.dir}/../..`;
const browserRunner = `${packageRoot}/tools/test/src/browser/run.ts`;

/** A module-backed e2e case (an `scripts/e2e-*.ts` file). */
function e2e(id: string, file: string, opts: Partial<CaseSpec> = {}): CaseSpec {
  return {
    id,
    exec: { kind: "module", modulePath: `${scriptsDir}/${file}` },
    ...opts,
  };
}

/** Tier names a consumer can pass to `--tier` / positionally. */
export const TIER_NAMES = [
  "unit",
  "integration",
  "tools",
  "coverage",
  "bdd",
  "e2e-cli",
  "e2e-relay",
  "browser",
  "e2e-mesh",
  "e2e-contract",
  "verify",
  "static",
] as const;

/** Tiers included by `--all` (everything realistic but not Docker-heavy). */
export const ALL_TIERS = [
  "unit",
  "integration",
  "tools",
  "coverage",
  "bdd",
  "e2e-cli",
  "e2e-relay",
  "browser",
  "e2e-mesh",
  "e2e-contract",
];

/** The fast inner loop run with no flags. */
export const DEFAULT_TIERS = ["unit", "integration"];

export function internalPlan(): TierPlan {
  const tiers: Tier[] = [
    {
      name: "unit",
      description: "pure logic + DOM via happy-dom (bun test)",
      cases: [
        {
          id: "unit.bun-test",
          // tests/unit/** — includes actions, quality, visual, contexts subdirs.
          exec: { kind: "command", argv: ["bun", "test", "unit"], cwd: `${packageRoot}/tests` },
        },
      ],
    },
    {
      name: "integration",
      description: "real modules wired together (bun test)",
      cases: [
        {
          id: "integration.bun-test",
          exec: {
            kind: "command",
            argv: ["bun", "test", "integration"],
            cwd: `${packageRoot}/tests`,
          },
        },
      ],
    },
    {
      // polly#173: these 994 tests ran in NO tier until now. `unit` and
      // `integration` both execute with cwd=packages/polly/tests, so everything
      // under tools/*/src/**/__tests__ was invisible to `bun run test`,
      // `test:all` and the pre-commit hook — the codegen and extractor suites
      // that are the only guard on `polly verify`'s correctness among them.
      //
      // Their own tier rather than `unit`: ~22s would roughly double the fast
      // inner loop, and these test the tooling, not the shipped runtime.
      // SKIP_DOCKER keeps the real-container suites out; they run in `verify`.
      name: "tools",
      description: "tooling suites (verify codegen, extraction, translation, test kit)",
      timeoutMs: 300_000,
      cases: [
        {
          id: "tools.verify-analysis",
          tags: ["tools", "verify", "codegen"],
          exec: {
            kind: "command",
            argv: ["bun", "test", "tools/verify/src", "tools/analysis/src"],
            cwd: packageRoot,
            env: { SKIP_DOCKER: "1" },
          },
        },
        {
          // The test kit itself — the tier engine's own helpers. Listed as a
          // path, like the case above: nothing globs tools/*, so a new suite
          // under a tools package runs in no tier until a case names it.
          id: "tools.test-kit",
          tags: ["tools", "test-kit"],
          exec: {
            kind: "command",
            argv: ["bun", "test", "tools/test/src"],
            cwd: packageRoot,
            env: { SKIP_DOCKER: "1" },
          },
        },
      ],
    },
    {
      name: "coverage",
      description: "per-file coverage policy + claimed-by exemptions (enforce-coverage.ts)",
      // 360s, not 180s. The case re-runs the whole unit suite under --coverage,
      // so its cost tracks that suite's size: measured at 150.0s / 154.8s /
      // 154.2s / 150.2s on this machine (2026-08-31, 1863 unit tests), it sat at
      // 83-86% of a 180s cap and then crossed it under load, failing an --all
      // run that had no coverage regression in it (polly#175). 360s is 2.3x the
      // slowest clean run and leaves it at 43% duty. The engine reports any case
      // above 70% of its budget, so the next erosion is visible before it is red.
      timeoutMs: 360_000,
      cases: [
        {
          // Re-runs the unit suite with --coverage and applies the policy in
          // scripts/coverage.config.ts. Self-spawns `bun test --coverage`, so
          // the ~15s overlap with the unit tier is intentional and cheap
          // against the full gate's Docker tiers.
          id: "coverage.enforce",
          tags: ["coverage", "policy"],
          exec: {
            kind: "command",
            // The consumer-facing engine, run against Polly's own config — the
            // same entry point `polly coverage` gives a consumer.
            argv: [
              "bun",
              `${packageRoot}/tools/test/src/coverage-policy/cli.ts`,
              "--config",
              `${scriptsDir}/coverage.config.ts`,
              "--no-mutate",
            ],
            cwd: packageRoot,
          },
        },
      ],
    },
    {
      name: "bdd",
      description: "executable Gherkin across the real factory boundary + verify cross-check",
      timeoutMs: 120_000,
      cases: [e2e("bdd.todo-list", "e2e-bdd.ts", { tags: ["bdd", "gherkin"] })],
    },
    {
      name: "e2e-cli",
      description: "real `polly` CLI from cold state (disk only)",
      concurrency: 2,
      timeoutMs: 300_000,
      // cost hints feed `--order` (coarse, not measured — tune from --json
      // durations): a full template build and the end-to-end coverage run are
      // the poles here; the quality pass is lighter.
      cases: [
        e2e("cli.init-build", "e2e-cli-init-build.ts", {
          tags: ["cli", "init", "build"],
          cost: "heavy",
        }),
        e2e("cli.quality", "e2e-cli-quality.ts", { tags: ["cli", "quality"] }),
        e2e("cli.coverage-consumer", "e2e-coverage-consumer.ts", {
          tags: ["cli", "coverage"],
          cost: "heavy",
        }),
      ],
    },
    {
      name: "e2e-relay",
      description: "in-process relay convergence (no browser)",
      cases: [
        e2e("relay.three-peer-convergence", "e2e-relay-three-peer-convergence.ts", {
          tags: ["relay", "convergence"],
        }),
      ],
    },
    {
      name: "browser",
      description: "real Chrome via Puppeteer (*.browser.ts)",
      timeoutMs: 180_000,
      cases: [
        {
          id: "browser.suite",
          needs: ["browser"],
          tags: ["browser", "webrtc", "ui"],
          exec: {
            kind: "command",
            argv: ["bun", browserRunner, "browser"],
            cwd: `${packageRoot}/tests`,
          },
        },
      ],
    },
    {
      name: "e2e-mesh",
      description: "multi-process peers over a real relay (Puppeteer)",
      concurrency: 2,
      timeoutMs: 240_000,
      // cost hints feed `--order` (coarse, not measured — tune from --json
      // durations): the multi-peer convergence and offline-catchup flows drive
      // the most wire traffic; a single gallery render is the cheapest.
      cases: [
        e2e("mesh.offline-online-drain", "e2e-mesh-offline-online-drain.ts", {
          needs: ["browser"],
          tags: ["mesh", "offline", "drain"],
          cost: "heavy",
        }),
        e2e("mesh.pairing-ceremony", "e2e-mesh-pairing-ceremony.ts", {
          needs: ["browser"],
          tags: ["mesh", "pairing"],
        }),
        e2e("mesh.blob-transfer", "e2e-mesh-blob-transfer.ts", {
          needs: ["browser"],
          tags: ["mesh", "blob"],
        }),
        e2e("mesh.three-peer-convergence", "e2e-mesh-three-peer-convergence.ts", {
          needs: ["browser"],
          tags: ["mesh", "convergence"],
          cost: "heavy",
        }),
        e2e("bdd.mesh-sync", "e2e-bdd-mesh.ts", {
          needs: ["browser"],
          tags: ["bdd", "mesh", "convergence", "gherkin"],
          cost: "heavy",
        }),
        e2e("mesh.revocation-prebaked", "e2e-mesh-revocation-prebaked.ts", {
          needs: ["browser"],
          tags: ["mesh", "revocation"],
        }),
        e2e("mesh.revocation-runtime", "e2e-mesh-revocation-runtime.ts", {
          needs: ["browser"],
          tags: ["mesh", "revocation"],
        }),
        e2e("mesh.revocation-propagation", "e2e-mesh-revocation-propagation.ts", {
          needs: ["browser"],
          tags: ["mesh", "revocation"],
        }),
        e2e("mesh.revocation-offline-catchup", "e2e-mesh-revocation-offline-catchup.ts", {
          needs: ["browser"],
          tags: ["mesh", "revocation"],
          cost: "heavy",
        }),
        e2e("mesh.corrupted-state-recovery", "e2e-mesh-corrupted-state-recovery.ts", {
          needs: ["browser"],
          tags: ["mesh", "recovery"],
        }),
        e2e("extension.storage", "e2e-extension-storage.ts", {
          needs: ["browser"],
          tags: ["extension", "storage", "mv3"],
        }),
        e2e("state.cross-tab-sync", "e2e-state-sync-cross-tab.ts", {
          needs: ["browser"],
          tags: ["state", "sync", "broadcast-channel"],
          cost: "light",
        }),
        e2e("elysia.offline-drain", "e2e-elysia-offline-drain.ts", {
          needs: ["browser"],
          tags: ["elysia", "offline", "drain"],
        }),
        e2e("gallery.render", "e2e-gallery.ts", {
          needs: ["browser"],
          tags: ["gallery", "ui", "visual"],
          cost: "light",
        }),
      ],
    },
    {
      name: "e2e-contract",
      description: "issue-contract harnesses over real node WebRTC (subprocess examples)",
      // Each case spawns examples/mesh-*/main.ts twice (post-fix + falsification
      // gate) over a bandwidth-throttled werift transport; the wire time IS the
      // test. Sequential on purpose: the #104 harness gates on event-loop tick
      // gaps, so a concurrent sibling chewing CPU would make it flaky. The
      // budget covers two 200s bun per-test timeouts, so a hung subprocess is
      // reported as a test failure rather than an opaque tier timeout.
      timeoutMs: 480_000,
      cases: [
        {
          id: "contract.mesh-large-initial-sync",
          tags: ["mesh", "contract", "webrtc"],
          exec: {
            kind: "command",
            argv: ["bun", "test", "e2e-contract/mesh-large-initial-sync.test.ts"],
            cwd: `${packageRoot}/tests`,
          },
        },
        {
          id: "contract.mesh-recovery-pair-stale-known-peers",
          tags: ["mesh", "contract", "webrtc"],
          exec: {
            kind: "command",
            argv: ["bun", "test", "e2e-contract/mesh-recovery-pair-stale-known-peers.test.ts"],
            cwd: `${packageRoot}/tests`,
          },
        },
      ],
    },
    {
      name: "verify",
      description: "TLA+/TLC + mutation (Docker)",
      timeoutMs: 600_000,
      // Every case here is a Docker TLC model-check or a mutation run — all
      // heavy, so `--order=cost` mostly just front-loads them uniformly.
      cases: [
        e2e("verify.codegen-roundtrip", "e2e-verify-codegen-roundtrip.ts", {
          needs: ["docker"],
          tags: ["verify", "tla"],
          cost: "heavy",
        }),
        e2e("verify.mesh-seed", "e2e-verify-mesh-seed.ts", {
          needs: ["docker"],
          tags: ["verify", "tla", "mesh"],
          cost: "heavy",
        }),
        e2e("verify.checked-in-specs", "e2e-verify-checked-in-specs.ts", {
          needs: ["docker"],
          tags: ["verify", "tla", "specs"],
          cost: "heavy",
        }),
        e2e("verify.liveness", "e2e-verify-liveness.ts", {
          needs: ["docker"],
          tags: ["verify", "tla", "liveness"],
          cost: "heavy",
        }),
        e2e("bdd.witness", "e2e-bdd-witness.ts", {
          needs: ["docker"],
          tags: ["verify", "tla", "bdd", "witness"],
          cost: "heavy",
        }),
        e2e("visualize.generate", "e2e-visualize.ts", {
          needs: ["docker"],
          tags: ["visualize"],
          cost: "heavy",
        }),
        e2e("visualize.export-serve", "e2e-visualize-export-serve.ts", {
          needs: ["docker"],
          tags: ["visualize", "serve"],
          cost: "heavy",
        }),
        e2e("stryker.verify", "e2e-stryker-verify.ts", {
          tags: ["stryker", "mutation"],
          cost: "heavy",
        }),
        {
          // The half of the `tools` tier that drives real containers: SANY
          // validation and the polly#173 container-leak guard. Without docker
          // these skip rather than pass spuriously.
          id: "verify.tools-docker",
          needs: ["docker"],
          tags: ["verify", "tools", "sany"],
          cost: "heavy",
          exec: {
            kind: "command",
            argv: [
              "bun",
              "test",
              "tools/verify/src/__tests__/validation/sany-integration.test.ts",
              "tools/verify/src/__tests__/runner",
              // polly#170: only the parser can catch a ternary translated into
              // unbalanced parentheses; asserting on the text cannot.
              "tools/verify/src/__tests__/codegen/object-literal-alias-ternary.test.ts",
            ],
            cwd: packageRoot,
          },
        },
      ],
    },
    {
      name: "static",
      description: "typecheck/lint/secrets/boundaries (check.ts)",
      timeoutMs: 600_000,
      cases: [
        {
          id: "static.check-all",
          tags: ["static", "lint", "typecheck"],
          exec: {
            kind: "command",
            argv: ["bun", `${scriptsDir}/check.ts`, "all"],
            cwd: packageRoot,
          },
        },
      ],
    },
  ];

  return { tiers };
}

export { packageRoot };
