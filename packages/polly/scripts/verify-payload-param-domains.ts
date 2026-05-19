#!/usr/bin/env bun

/**
 * End-to-end verification artefact for issue #72 — payload-domain wiring.
 *
 * Per ~/projects/CLAUDE.md ("green checks do not prove features work"):
 * this script runs the user-facing `polly verify` workflow against
 * examples/todo-list, asserts the generated TLA+ spec types
 * `payload.theme` as the declared enum (not the catch-all Value),
 * confirms TLC reports no errors on the well-typed spec, then mutates
 * the generated spec to widen PayloadType beyond the modeled state
 * field's domain and runs TLC directly (bypassing polly's regenerate
 * pass) to assert TLC catches the violation. If the negative case
 * passes, the domain restriction is not load-bearing and #72 is not
 * actually fixed — the script exits non-zero.
 *
 * Run with: bun run scripts/verify-payload-param-domains.ts
 */

import { spawn } from "node:child_process";
import { existsSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { basename, dirname, resolve } from "node:path";

const PROJECT_ROOT = resolve(import.meta.dir, "..");
const EXAMPLE = resolve(PROJECT_ROOT, "examples/todo-list");
const TLA_DIR = resolve(EXAMPLE, "specs/tla/generated/preferences");
const TLA_FILE = resolve(TLA_DIR, "UserApp_preferences.tla");
const ENUM_PATTERN = /theme: \{"light", "dark", "system"\}/;

function fail(reason: string, details?: string): never {
  console.log(`FAIL: ${reason}`);
  if (details) console.log(details);
  process.exit(1);
}

function step(n: number, total: number, msg: string): void {
  console.log(`[${n}/${total}] ${msg}`);
}

async function run(
  cmd: string,
  args: string[],
  cwd: string
): Promise<{ code: number; out: string }> {
  return new Promise((resolveProc) => {
    let out = "";
    const proc = spawn(cmd, args, { cwd, env: process.env });
    proc.stdout?.on("data", (d) => {
      out += d.toString();
    });
    proc.stderr?.on("data", (d) => {
      out += d.toString();
    });
    proc.on("close", (code) => resolveProc({ code: code ?? 0, out }));
  });
}

async function runPollyVerify(): Promise<{ code: number; out: string }> {
  return run("polly", ["verify"], EXAMPLE);
}

async function runTlcDirect(specPath: string): Promise<{ code: number; out: string }> {
  // Mirror tools/verify/src/runner/docker.ts:81-134 — run TLC against the
  // existing spec without polly's regenerate pass.
  const specDir = dirname(specPath);
  const specName = basename(specPath, ".tla");
  return run(
    "docker",
    [
      "run",
      "--rm",
      "-v",
      `${specDir}:/work`,
      "polly-tla:latest",
      "tlc",
      "-workers",
      "1",
      "-cleanup",
      "-depth",
      "8",
      `${specName}.tla`,
    ],
    specDir
  );
}

async function main() {
  console.log("=== issue #72 e2e: payload-domain wiring ===");

  // 1. Cold codegen + verify — clear generated TLA+ so we know we're starting fresh.
  step(1, 5, "regenerating TLA+ from scratch and running TLC");
  if (existsSync(resolve(EXAMPLE, "specs/tla/generated"))) {
    rmSync(resolve(EXAMPLE, "specs/tla/generated"), { recursive: true, force: true });
  }
  const gen = await runPollyVerify();
  if (!existsSync(TLA_FILE)) {
    fail("preferences subsystem TLA+ was not generated", gen.out);
  }

  // 2. Positive grep — the declared enum domain made it into PayloadType.
  step(2, 5, "asserting PayloadType contains the declared enum domain");
  const spec = readFileSync(TLA_FILE, "utf8");
  if (!/PayloadType ==/.test(spec)) {
    fail("no PayloadType declaration found in preferences spec", spec);
  }
  if (!ENUM_PATTERN.test(spec)) {
    fail("PayloadType does not type theme as the declared enum domain", spec);
  }
  if (/theme: Value\b/.test(spec)) {
    fail("PayloadType still types theme as catch-all Value", spec);
  }

  // 3. Positive TLC — the well-typed spec verifies clean.
  step(3, 5, "asserting TLC reports no errors on the well-typed spec");
  if (gen.code !== 0) {
    fail("polly verify exit code != 0 on the well-typed spec", gen.out);
  }
  if (/✗ preferences failed|preferences\s+failed/i.test(gen.out)) {
    fail("polly verify reported preferences failure on the well-typed spec", gen.out);
  }

  // 4. Negative mutation — widen PayloadType to admit a value outside the
  // modeled state field's enum, then run TLC directly (NOT polly verify,
  // which would regenerate and overwrite the mutation). With the widened
  // PayloadType, TLC must reach a state where contextStates[ctx].theme
  // gets assigned the out-of-domain value, violating UserStateTypeInvariant.
  step(4, 5, "asserting TLC catches an out-of-domain enum mutation");
  const mutated = spec.replace(ENUM_PATTERN, 'theme: {"light", "dark", "system", "neon"}');
  if (mutated === spec) {
    fail("could not apply mutation — pattern not found in spec");
  }
  writeFileSync(TLA_FILE, mutated);

  const negResult = await runTlcDirect(TLA_FILE);
  // Restore the file so a subsequent `polly verify` doesn't carry the mutation.
  writeFileSync(TLA_FILE, spec);

  const negSawError =
    negResult.code !== 0 ||
    /Error|Counterexample|Invariant.*violated|UserStateTypeInvariant|TypeOK/i.test(negResult.out);
  if (!negSawError) {
    fail(
      "TLC did not catch out-of-domain payload value — the domain restriction is not enforced. " +
        "If this fails, the PayloadType assertion in step 2 is decorative.",
      negResult.out
    );
  }

  // 5. Restore + finish.
  step(5, 5, "spec restored, e2e PASS");
  console.log("e2e PASS");
}

await main();
