#!/usr/bin/env bun

/**
 * Polly publish orchestrator — `bun run publish:public`.
 *
 * Replaces a brittle one-liner whose two flaws were:
 *
 *   1. The OTP was expanded by the shell *before* the publish ran. With
 *      `prepublishOnly` running typecheck/lint/test/build first, the
 *      30-second TOTP code had long expired by the time `npm publish`
 *      actually fired, so npm rejected it.
 *   2. Nothing checked the local version against the registry, so a
 *      forgotten version bump only surfaced *after* the whole gauntlet
 *      of checks had run — minutes wasted on a guaranteed failure.
 *
 * This script runs the cheap, fail-fast version gate first, then the
 * checks, and only mints the OTP in the final second before publish.
 *
 * `npm publish` is invoked with `--ignore-scripts` so `prepublishOnly`
 * does not re-run the checks. `prepublishOnly` is kept in package.json
 * purely as a backstop for anyone who runs `npm publish` directly.
 */

import { join } from "node:path";

const PKG_DIR = join(import.meta.dir, "..");
const PKG_NAME = "@fairfox/polly";

interface RunResult {
  code: number;
  stdout: string;
  stderr: string;
}

async function run(args: string[], opts: { quiet?: boolean } = {}): Promise<RunResult> {
  const proc = Bun.spawn(args, {
    cwd: PKG_DIR,
    stdout: opts.quiet ? "pipe" : "inherit",
    stderr: opts.quiet ? "pipe" : "inherit",
  });
  const stdout = opts.quiet ? await new Response(proc.stdout).text() : "";
  const stderr = opts.quiet ? await new Response(proc.stderr).text() : "";
  await proc.exited;
  return { code: proc.exitCode ?? 1, stdout, stderr };
}

function fail(msg: string): never {
  process.stderr.write(`\n❌ ${msg}\n`);
  process.exit(1);
}

// 1. Version gate ────────────────────────────────────────────────────────────
const pkg = await Bun.file(join(PKG_DIR, "package.json")).json();
const localVersion: string = pkg.version;
process.stdout.write(`📦 ${PKG_NAME} local version:     ${localVersion}\n`);

const view = await run(["npm", "view", PKG_NAME, "version"], { quiet: true });
if (view.code === 0) {
  const publishedVersion = view.stdout.trim();
  process.stdout.write(`🌐 ${PKG_NAME} published version: ${publishedVersion}\n`);
  if (Bun.semver.order(localVersion, publishedVersion) <= 0) {
    fail(
      `Local version ${localVersion} is not greater than published ` +
        `${publishedVersion}.\n   Bump the version in package.json before publishing.`
    );
  }
} else if (/E?404/.test(view.stderr)) {
  // A genuinely unpublished package returns a 404; anything else (offline,
  // auth, registry outage) should abort rather than be mistaken for one.
  process.stdout.write(`🌐 ${PKG_NAME} not yet published — first release.\n`);
} else {
  fail(`Could not query the registry for ${PKG_NAME}:\n${view.stderr.trim()}`);
}
process.stdout.write(`✅ Version ${localVersion} is publishable.\n`);

// 2. Checks ──────────────────────────────────────────────────────────────────
const steps: Array<[string, string[]]> = [
  ["Typecheck", ["bun", "run", "typecheck"]],
  ["Lint", ["bun", "run", "lint"]],
  ["Tests", ["bun", "run", "--cwd", "tests", "test"]],
  ["Build", ["bun", "run", "build:lib"]],
];

for (const [label, args] of steps) {
  process.stdout.write(`\n▶ ${label}…\n`);
  const { code } = await run(args);
  if (code !== 0) fail(`${label} failed — aborting publish.`);
  process.stdout.write(`✅ ${label} passed.\n`);
}

// 3. Fresh OTP, then publish ─────────────────────────────────────────────────
process.stdout.write("\n🔑 Minting a fresh OTP…\n");
const otpResult = await run(
  [
    "pass-cli",
    "item",
    "totp",
    "--output",
    "json",
    "--item-id",
    "Rdr--oUgHp-IfyjoTB7vhMPHfNt6Oz2JpXfS1WrdQMQ9damDMPOvKiOxxpCZqp92WgqXnfY68cSXWdQ_JVMNMQ==",
    "--share-id",
    "Ixmpll6U5ioU_1P4fzUbarQNANRPU51O68xzFblTB08S0HUfw4dhQaNAv4Yv7Sud_Vf8ps4mnQUFqdvN-eTRdQ==",
  ],
  { quiet: true }
);
if (otpResult.code !== 0) {
  fail(`pass-cli could not retrieve the OTP:\n${otpResult.stderr.trim()}`);
}
let otp: string | undefined;
try {
  otp = JSON.parse(otpResult.stdout).totp;
} catch {
  fail("pass-cli did not return parseable JSON for the OTP.");
}
if (!otp) fail("pass-cli returned an empty OTP.");

process.stdout.write(`\n🚀 Publishing ${PKG_NAME}@${localVersion}…\n`);
const { code } = await run([
  "npm",
  "publish",
  "--access",
  "public",
  "--ignore-scripts",
  `--otp=${otp}`,
]);
if (code !== 0) fail("npm publish failed.");
process.stdout.write(`\n✅ Published ${PKG_NAME}@${localVersion}.\n`);
