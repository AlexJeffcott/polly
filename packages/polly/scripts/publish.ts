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
 * The OTP step is the one part that depends on a remote service, and the
 * Proton Pass API does time out. A single failure there used to discard a
 * passing check run, so the step now: bounds each `pass-cli` call, retries
 * it, refuses a code that is about to expire, and falls back to a typed
 * code rather than aborting. `POLLY_NPM_OTP` skips the lookup entirely.
 *
 * `npm publish` is invoked with `--ignore-scripts` so `prepublishOnly`
 * does not re-run the checks. `prepublishOnly` is kept in package.json
 * purely as a backstop for anyone who runs `npm publish` directly.
 */

import { join } from "node:path";
import { createInterface } from "node:readline/promises";

const PKG_DIR = join(import.meta.dir, "..");
const PKG_NAME = "@fairfox/polly";

/** Proton Pass coordinates of the npm TOTP item. */
const PASS_ITEM_ID =
  "Rdr--oUgHp-IfyjoTB7vhMPHfNt6Oz2JpXfS1WrdQMQ9damDMPOvKiOxxpCZqp92WgqXnfY68cSXWdQ_JVMNMQ==";
const PASS_SHARE_ID =
  "Ixmpll6U5ioU_1P4fzUbarQNANRPU51O68xzFblTB08S0HUfw4dhQaNAv4Yv7Sud_Vf8ps4mnQUFqdvN-eTRdQ==";

/** pass-cli's own timeout is ~30s — longer than the TOTP window it fetches. */
const OTP_TIMEOUT_MS = 10_000;
const OTP_ATTEMPTS = 3;
const OTP_RETRY_DELAY_MS = 1_000;
/** Below this, the code expires before npm finishes the upload. */
const OTP_MIN_SECONDS_LEFT = 5;
const TOTP_PERIOD_SECONDS = 30;

interface RunResult {
  code: number;
  stdout: string;
  stderr: string;
}

async function run(
  args: string[],
  opts: { quiet?: boolean; timeoutMs?: number } = {}
): Promise<RunResult> {
  const proc = Bun.spawn(args, {
    cwd: PKG_DIR,
    // npm publish prompts for an OTP itself when one is not supplied.
    stdin: opts.quiet ? "ignore" : "inherit",
    stdout: opts.quiet ? "pipe" : "inherit",
    stderr: opts.quiet ? "pipe" : "inherit",
  });

  const collect: Promise<RunResult> = (async () => {
    const stdout = opts.quiet ? await new Response(proc.stdout).text() : "";
    const stderr = opts.quiet ? await new Response(proc.stderr).text() : "";
    await proc.exited;
    return { code: proc.exitCode ?? 1, stdout, stderr };
  })().catch((err) => ({ code: 1, stdout: "", stderr: String(err) }));

  if (!opts.timeoutMs) return await collect;

  // The timeout is a race, not a kill-then-wait: killing a process whose own
  // child still holds the stdout pipe leaves the read pending for ever, and a
  // publish script that hangs is worse than one that fails.
  let timer: ReturnType<typeof setTimeout> | undefined;
  const expiry = new Promise<RunResult>((resolve) => {
    timer = setTimeout(() => {
      proc.kill();
      proc.unref();
      resolve({ code: 124, stdout: "", stderr: `timed out after ${opts.timeoutMs} ms` });
    }, opts.timeoutMs);
  });

  try {
    return await Promise.race([collect, expiry]);
  } finally {
    clearTimeout(timer);
  }
}

function fail(msg: string): never {
  process.stderr.write(`\n❌ ${msg}\n`);
  process.exit(1);
}

const sleep = (ms: number) => new Promise((resolve) => setTimeout(resolve, ms));

/** Seconds a code minted now still has, on the standard 30s TOTP window. */
function secondsLeftInWindow(): number {
  return TOTP_PERIOD_SECONDS - (Math.floor(Date.now() / 1000) % TOTP_PERIOD_SECONDS);
}

/** One pass-cli lookup. Returns the code, or a reason it failed. */
async function fetchOtpFromPass(): Promise<{ otp?: string; reason?: string }> {
  const result = await run(
    [
      "pass-cli",
      "item",
      "totp",
      "--output",
      "json",
      "--item-id",
      PASS_ITEM_ID,
      "--share-id",
      PASS_SHARE_ID,
    ],
    { quiet: true, timeoutMs: OTP_TIMEOUT_MS }
  );
  if (result.code !== 0) {
    return { reason: result.stderr.trim() || `pass-cli exited ${result.code}` };
  }
  let otp: unknown;
  try {
    otp = JSON.parse(result.stdout).totp;
  } catch {
    return { reason: "pass-cli did not return parseable JSON" };
  }
  if (typeof otp !== "string" || !/^\d{6,8}$/.test(otp)) {
    return { reason: "pass-cli returned no usable code" };
  }
  return { otp };
}

/** Last resort: the code off the phone, so a passing check run is not wasted. */
async function promptForOtp(): Promise<string> {
  if (!process.stdin.isTTY) {
    fail(
      "Could not retrieve the OTP from Proton Pass and stdin is not a terminal.\n" +
        "   Re-run interactively, or set POLLY_NPM_OTP=<code>."
    );
  }
  const rl = createInterface({ input: process.stdin, output: process.stdout });
  try {
    for (let attempt = 0; attempt < 3; attempt++) {
      let answer: string;
      try {
        answer = (await rl.question("   Enter the npm OTP by hand: ")).trim();
      } catch {
        // Ctrl+D or a closed stdin rejects the question; that is a cancel,
        // not a crash, so report it as one rather than as a stack trace.
        break;
      }
      if (/^\d{6,8}$/.test(answer)) return answer;
      process.stdout.write("   That is not a 6–8 digit code.\n");
    }
  } finally {
    rl.close();
  }
  fail("No valid OTP entered.");
}

async function mintOtp(): Promise<string> {
  const fromEnv = process.env["POLLY_NPM_OTP"]?.trim();
  if (fromEnv) {
    process.stdout.write("   Using POLLY_NPM_OTP from the environment.\n");
    return fromEnv;
  }

  for (let attempt = 1; attempt <= OTP_ATTEMPTS; attempt++) {
    // A code minted in the last seconds of its window expires mid-upload.
    const left = secondsLeftInWindow();
    if (left < OTP_MIN_SECONDS_LEFT) {
      process.stdout.write(`   Window has ${left}s left — waiting for the next one…\n`);
      await sleep((left + 1) * 1000);
    }

    const { otp, reason } = await fetchOtpFromPass();
    if (otp) return otp;

    process.stdout.write(
      `   pass-cli attempt ${attempt}/${OTP_ATTEMPTS} failed: ${reason?.split("\n")[0]}\n`
    );
    if (attempt < OTP_ATTEMPTS) await sleep(OTP_RETRY_DELAY_MS);
  }

  process.stdout.write(
    "\n⚠️  Proton Pass did not answer. The checks all passed, so the publish\n" +
      "   does not have to be thrown away — type the code instead.\n"
  );
  return await promptForOtp();
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
const otp = await mintOtp();

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
