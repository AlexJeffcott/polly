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
  "e2e-cli",
  "e2e-relay",
  "browser",
  "e2e-mesh",
  "verify",
  "static",
] as const;

/** Tiers included by `--all` (everything realistic but not Docker-heavy). */
export const ALL_TIERS = ["unit", "integration", "e2e-cli", "e2e-relay", "browser", "e2e-mesh"];

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
      name: "e2e-cli",
      description: "real `polly` CLI from cold state (disk only)",
      concurrency: 2,
      timeoutMs: 300_000,
      cases: [
        e2e("cli.init-build", "e2e-cli-init-build.ts", { tags: ["cli", "init", "build"] }),
        e2e("cli.quality", "e2e-cli-quality.ts", { tags: ["cli", "quality"] }),
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
      cases: [
        e2e("mesh.offline-online-drain", "e2e-mesh-offline-online-drain.ts", {
          needs: ["browser"],
          tags: ["mesh", "offline", "drain"],
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
        }),
        e2e("mesh.corrupted-state-recovery", "e2e-mesh-corrupted-state-recovery.ts", {
          needs: ["browser"],
          tags: ["mesh", "recovery"],
        }),
        e2e("extension.storage", "e2e-extension-storage.ts", {
          needs: ["browser"],
          tags: ["extension", "storage", "mv3"],
        }),
        e2e("elysia.offline-drain", "e2e-elysia-offline-drain.ts", {
          needs: ["browser"],
          tags: ["elysia", "offline", "drain"],
        }),
      ],
    },
    {
      name: "verify",
      description: "TLA+/TLC + mutation (Docker)",
      timeoutMs: 600_000,
      cases: [
        e2e("verify.codegen-roundtrip", "e2e-verify-codegen-roundtrip.ts", {
          needs: ["docker"],
          tags: ["verify", "tla"],
        }),
        e2e("verify.mesh-seed", "e2e-verify-mesh-seed.ts", {
          needs: ["docker"],
          tags: ["verify", "tla", "mesh"],
        }),
        e2e("visualize.generate", "e2e-visualize.ts", {
          needs: ["docker"],
          tags: ["visualize"],
        }),
        e2e("visualize.export-serve", "e2e-visualize-export-serve.ts", {
          needs: ["docker"],
          tags: ["visualize", "serve"],
        }),
        e2e("stryker.verify", "e2e-stryker-verify.ts", { tags: ["stryker", "mutation"] }),
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
