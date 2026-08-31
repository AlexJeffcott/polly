#!/usr/bin/env bun
/**
 * E2e: every checked-in `.tla`/`.cfg` pair must actually run (polly#172).
 *
 * `specs/README.md` documents `tlc MessageRouter.tla -config MessageRouter.cfg`
 * and `specs/tla/README.md` documents the docker-compose equivalent. Nothing in
 * the repo ran either: `MessageRouter.tla` is used only as a module the
 * generated `UserApp_*` specs EXTEND, and those carry their own `.cfg`. So the
 * documented command had never been executed, and it did not work —
 * `MessageRouter.cfg` declared an inline `CONSTRAINT` expression where TLC
 * requires a defined operator, and both PROPERTIES quantified over a VARIABLE,
 * which TLC refuses outright.
 *
 * The properties had been written as documentation of intent and never run, so
 * no error was ever seen. This closes that: a reader following the README gets
 * a model that checks.
 *
 * Needs: Docker and the `polly-tla:latest` image.
 */

export const capability = "verify.checked-in-specs" as const;

import { copyFileSync, existsSync, mkdtempSync, readdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, resolve } from "node:path";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { mintContainerName } from "../tools/verify/src/runner/container-name";
import { removeContainer } from "../tools/verify/src/runner/docker";

const DOCKER_IMAGE = "polly-tla:latest";
const SPEC_DIR = resolve(import.meta.dir, "../tools/verify/specs/tla");

/**
 * How long to let each model run before concluding it is healthy.
 *
 * The polly#172 defect class is TLC REJECTING the model — an inline CONSTRAINT
 * expression where a defined operator is required, a temporal formula
 * quantifying over a variable, a missing operator. Every one of those is
 * reported within the first seconds, before exploration begins. So a short cap
 * catches the whole class, and a model still running when the cap expires has
 * demonstrated exactly what this harness is for.
 *
 * A full check is not affordable here: MessageRouter.cfg declares
 * MaxMessages = 4 over 3 contexts and 3 tabs, and SendMessage quantifies over
 * every non-empty subset of contexts, so the real model runs to over a million
 * distinct states. `specs/tla/README.md` documents the small constants to use
 * when checking the properties themselves.
 */
const RUN_CAP_MS = 45_000;

async function runTLC(workDir: string, spec: string): Promise<string> {
  // Named so the cap below can remove the container: `--rm` only fires when a
  // container exits, and killing the client never kills the container
  // (polly#173).
  const containerName = mintContainerName(`spec-${spec}`);
  const proc = Bun.spawn(
    [
      "docker",
      "run",
      "--rm",
      "--name",
      containerName,
      "-v",
      `${workDir}:/work`,
      DOCKER_IMAGE,
      "tlc",
      "-workers",
      "1",
      "-cleanup",
      "-config",
      `${spec}.cfg`,
      `${spec}.tla`,
    ],
    { stdout: "pipe", stderr: "pipe" }
  );

  const capped = setTimeout(() => {
    proc.kill("SIGKILL");
    removeContainer(containerName);
  }, RUN_CAP_MS);

  try {
    const [stdout, stderr] = await Promise.all([
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
    ]);
    await proc.exited;
    return `${stdout}\n${stderr}`;
  } finally {
    clearTimeout(capped);
  }
}

/**
 * The failures polly#172 is about: TLC rejecting the configuration or the spec
 * before it can check anything. A property VIOLATION is a different outcome and
 * is not this harness's business.
 */
const REJECTIONS = [
  /is either undefined or not an operator/i,
  /was not found|Unknown operator/i,
  /Attempted to check equality|TLC threw an unexpected exception/i,
  /Error: Failed to parse|parse error/i,
  /The constraint .* is not/i,
  /Semantic errors/i,
];

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    const specs = readdirSync(SPEC_DIR)
      .filter((f) => f.endsWith(".tla"))
      .map((f) => basename(f, ".tla"))
      .filter((name) => existsSync(join(SPEC_DIR, `${name}.cfg`)))
      .sort();

    assert(specs.length > 0, `no .tla/.cfg pairs found in ${SPEC_DIR}`);
    ctx.log(`[e2e] checking ${specs.length} checked-in spec pairs: ${specs.join(", ")}`);

    for (const spec of specs) {
      const work = mkdtempSync(join(tmpdir(), `polly-spec-${spec}-`));
      try {
        // Copy every module: a spec may EXTEND a sibling.
        for (const file of readdirSync(SPEC_DIR)) {
          if (file.endsWith(".tla") || file.endsWith(".cfg")) {
            copyFileSync(join(SPEC_DIR, file), join(work, file));
          }
        }

        const output = await runTLC(work, spec);

        const rejection = REJECTIONS.find((pattern) => pattern.test(output));
        assert(
          rejection === undefined,
          `TLC rejected the checked-in ${spec}.tla/${spec}.cfg pair ` +
            `(matched ${rejection}). The command documented in specs/README.md ` +
            `does not work.\n${output}`
        );

        // TLC must have got far enough to prove it accepted the config, rather
        // than dying silently or producing nothing at all.
        assert(
          /Computing initial states|Finished computing initial states|states generated/i.test(
            output
          ),
          `TLC produced no exploration output for ${spec} — it did not accept the ` +
            `model.\n${output}`
        );
        ctx.log(`[e2e]   ${spec}: TLC accepted the model and began checking`);
      } finally {
        rmSync(work, { recursive: true, force: true });
      }
    }

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
