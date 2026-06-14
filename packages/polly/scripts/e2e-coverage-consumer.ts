#!/usr/bin/env bun
/**
 * E2e: `polly coverage` from a consumer's cold state.
 *
 * The coverage engine is consumer-facing, so it must be proven against the
 * entry point a fresh consumer actually uses — a directory with its own
 * source and tests and no Polly internals — not against Polly's own hand-wired
 * config. This builds a throwaway project in a temp dir and drives the shipped
 * CLI through the paths a consumer hits:
 *
 *   1. zero-config, fully covered      → report-only, passes
 *   2. an orphan source file           → advisory by default, fails --strict-orphans
 *   3. a coverage.config.ts floor      → a below-floor file fails
 *   4. an exemption with a real claim  → passes
 *   5. an exemption with a dead claim  → fails
 *
 * Run in one command: `bun scripts/e2e-coverage-consumer.ts`.
 */

import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

export const capability = "coverage.consumer" as const;

const CLI = `${import.meta.dir}/../tools/test/src/coverage-policy/cli.ts`;

interface CliOutcome {
  code: number;
  out: string;
}

async function runCli(cwd: string, args: string[]): Promise<CliOutcome> {
  const proc = Bun.spawn(["bun", CLI, ...args], { cwd, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  const code = await proc.exited;
  return { code, out: `${stdout}\n${stderr}` };
}

function write(root: string, rel: string, body: string): void {
  writeFileSync(join(root, rel), body);
}

function expect(cond: boolean, detail: string): void {
  if (!cond) throw new Error(`assertion failed: ${detail}`);
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const root = mkdtempSync(join(tmpdir(), "polly-cov-consumer-"));
  try {
    mkdirSync(join(root, "src"), { recursive: true });

    write(root, "src/greet.ts", 'export const greet = (n: string): string => "hi " + n;\n');
    write(
      root,
      "greet.test.ts",
      'import { test, expect } from "bun:test";\nimport { greet } from "./src/greet.ts";\ntest("greet", () => { expect(greet("a")).toBe("hi a"); });\n'
    );

    ctx.log("[e2e] 1. zero-config, fully covered");
    const covered = await runCli(root, []);
    expect(covered.code === 0, `zero-config should pass, got ${covered.code}: ${covered.out}`);
    expect(covered.out.includes("report-only"), "zero-config should be report-only");

    ctx.log("[e2e] 2. orphan source file");
    write(root, "src/orphan.ts", "export const unused = () => 42;\n");
    const advisory = await runCli(root, []);
    expect(advisory.code === 0, "orphan is advisory by default");
    expect(advisory.out.includes("no unit test imports"), "orphan should be reported");
    const strict = await runCli(root, ["--strict-orphans"]);
    expect(strict.code === 1, "--strict-orphans should fail on an orphan");
    rmSync(join(root, "src/orphan.ts"));

    ctx.log("[e2e] 3. a coverage.config.ts floor catches a below-floor file");
    write(
      root,
      "src/partial.ts",
      "export const used = () => 1;\nexport const notused = () => 2;\n"
    );
    write(
      root,
      "partial.test.ts",
      'import { test, expect } from "bun:test";\nimport { used } from "./src/partial.ts";\ntest("used", () => { expect(used()).toBe(1); });\n'
    );
    write(
      root,
      "coverage.config.ts",
      "export const config = { defaultThreshold: { lines: 80, funcs: 80 } };\n"
    );
    const violating = await runCli(root, []);
    expect(violating.code === 1, "below-floor file should fail");
    expect(violating.out.includes("src/partial.ts"), "the violating file should be named");

    ctx.log("[e2e] 4. an exemption with a real claimedBy passes");
    write(
      root,
      "coverage.config.ts",
      'export const config = { defaultThreshold: { lines: 80, funcs: 80 }, exempt: { "src/partial.ts": { reason: "half is e2e-only", claimedBy: "greet.test.ts" } } };\n'
    );
    const exempted = await runCli(root, []);
    expect(exempted.code === 0, `real claimedBy should pass: ${exempted.out}`);

    ctx.log("[e2e] 5. an exemption with a dead claimedBy fails");
    write(
      root,
      "coverage.config.ts",
      'export const config = { defaultThreshold: { lines: 80, funcs: 80 }, exempt: { "src/partial.ts": { reason: "x", claimedBy: "nope.test.ts" } } };\n'
    );
    const deadClaim = await runCli(root, []);
    expect(deadClaim.code === 1, "dead claimedBy should fail");
    expect(deadClaim.out.includes("claimedBy missing"), "should name the missing claim");

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
