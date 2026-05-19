/**
 * `polly quality attest` — sign a passing run and post a GitHub commit status.
 *
 * The flow:
 *   1. Refuse on a dirty working tree (porcelain non-empty).
 *   2. Resolve the current commit sha and the gh user.
 *   3. Run every registered check via the cache. A red result aborts
 *      with no status posted.
 *   4. Compute a digest of the commit sha plus a sorted summary of
 *      check results.
 *   5. Post a GitHub commit status named `polly/attested/<user>` to
 *      that sha via the local `gh` CLI (which carries the user's
 *      existing authentication).
 *   6. Cache the signed entry at
 *      `.cache/polly-quality/attest/<commit>.json` so a re-invocation
 *      on the same commit short-circuits to a status refresh.
 *
 * Auth lives in the user's `gh` CLI install rather than a `GITHUB_TOKEN`
 * env var: every contributor running `polly quality attest` already
 * authenticated `gh` for issue and PR work, and shelling out keeps the
 * dependency surface zero.
 */

import { createHash } from "node:crypto";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { type RegisteredCheck, runChecks } from "./host";
import type { CheckRunResult, QualityRunConfig, RunReport } from "./types";

export type AttestOptions = {
  rootDir: string;
  registry: Map<string, RegisteredCheck>;
  runConfig: QualityRunConfig;
  /**
   * When set, the deploy preflight command (read from
   * `runConfig.attestDeploy`) runs before the post and the status
   * name becomes `polly/deploy-attested/<user>`.
   */
  deploy?: boolean;
  /** Override for the `polly` segment of the status context. */
  contextPrefix?: string;
};

export type AttestResult = {
  ok: boolean;
  /** Posted (or would-have-posted) status context. */
  context: string;
  /** Commit sha the status was attached to. */
  sha: string;
  /** Fingerprint of the run. */
  digest: string;
  /** Summary lines for the CLI reporter. */
  messages: string[];
  /** When non-empty, attest aborted before posting. */
  error?: string;
  /** Underlying check report for downstream display. */
  report?: RunReport;
};

async function spawnText(args: string[], cwd: string): Promise<{ ok: boolean; out: string }> {
  const proc = Bun.spawn(args, { cwd, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  return { ok: proc.exitCode === 0, out: `${stdout}${stderr}` };
}

async function workingTreeIsClean(rootDir: string): Promise<boolean> {
  const r = await spawnText(["git", "status", "--porcelain"], rootDir);
  if (!r.ok) return false;
  return r.out.trim().length === 0;
}

async function currentCommit(rootDir: string): Promise<string | null> {
  const r = await spawnText(["git", "rev-parse", "HEAD"], rootDir);
  if (!r.ok) return null;
  const sha = r.out.trim();
  if (!/^[0-9a-f]{40}$/.test(sha)) return null;
  return sha;
}

async function ghUser(rootDir: string): Promise<string | null> {
  const r = await spawnText(["gh", "api", "user", "--jq", ".login"], rootDir);
  if (!r.ok) return null;
  const login = r.out.trim();
  return login.length > 0 ? login : null;
}

async function ghRepoSlug(rootDir: string): Promise<string | null> {
  const r = await spawnText(
    ["gh", "repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner"],
    rootDir
  );
  if (!r.ok) return null;
  const slug = r.out.trim();
  if (!slug.includes("/")) return null;
  return slug;
}

export function summariseRunReport(report: RunReport): string {
  const passed = report.results.filter((r) => r.ok).length;
  const total = report.results.length;
  return `${passed}/${total} checks passed`;
}

export function digestRun(sha: string, results: CheckRunResult[]): string {
  // Stable per-id ordering plus the run-relevant fields. We deliberately
  // exclude durationMs and cached so a cache-warmed re-attest produces the
  // same digest as the original.
  const stable = results
    .slice()
    .sort((a, b) => a.id.localeCompare(b.id))
    .map((r) => ({ id: r.id, ok: r.ok, messages: r.messages }));
  const payload = JSON.stringify({ sha, results: stable });
  return createHash("sha256").update(payload).digest("hex");
}

function attestCachePath(rootDir: string, sha: string): string {
  return join(rootDir, ".cache", "polly-quality", "attest", `${sha}.json`);
}

async function readPriorAttestation(rootDir: string, sha: string): Promise<string | null> {
  try {
    const raw = await readFile(attestCachePath(rootDir, sha), "utf8");
    const parsed = JSON.parse(raw) as unknown as { digest?: string };
    return parsed.digest ?? null;
  } catch {
    return null;
  }
}

async function writeAttestation(
  rootDir: string,
  sha: string,
  context: string,
  digest: string
): Promise<void> {
  const path = attestCachePath(rootDir, sha);
  await mkdir(join(path, ".."), { recursive: true });
  const entry = {
    sha,
    context,
    digest,
    attestedAt: new Date().toISOString(),
  };
  await writeFile(path, JSON.stringify(entry, null, 2));
}

async function postCommitStatus(
  rootDir: string,
  slug: string,
  sha: string,
  context: string,
  description: string
): Promise<{ ok: boolean; output: string }> {
  const r = await spawnText(
    [
      "gh",
      "api",
      "-X",
      "POST",
      `repos/${slug}/statuses/${sha}`,
      "-f",
      "state=success",
      "-f",
      `context=${context}`,
      "-f",
      `description=${description}`,
    ],
    rootDir
  );
  return { ok: r.ok, output: r.out };
}

async function preflightOk(
  rootDir: string
): Promise<{ ok: boolean; reason?: string; sha?: string }> {
  if (!(await workingTreeIsClean(rootDir))) {
    return { ok: false, reason: "Working tree is dirty; commit or stash before attesting." };
  }
  const sha = await currentCommit(rootDir);
  if (!sha) return { ok: false, reason: "Could not resolve current commit (is this a git repo?)" };
  return { ok: true, sha };
}

async function resolveContext(
  rootDir: string,
  deploy: boolean,
  contextPrefix: string
): Promise<{ ok: boolean; reason?: string; context?: string; user?: string }> {
  const user = await ghUser(rootDir);
  if (!user) return { ok: false, reason: "gh CLI is not authenticated; run `gh auth login`." };
  const action = deploy ? "deploy-attested" : "attested";
  return { ok: true, user, context: `${contextPrefix}/${action}/${user}` };
}

export async function runAttest(opts: AttestOptions): Promise<AttestResult> {
  const contextPrefix = opts.contextPrefix ?? "polly";
  const pre = await preflightOk(opts.rootDir);
  if (!pre.ok || !pre.sha) {
    return {
      ok: false,
      context: "",
      sha: "",
      digest: "",
      messages: [],
      error: pre.reason,
    };
  }
  const sha = pre.sha;

  const ctx = await resolveContext(opts.rootDir, opts.deploy === true, contextPrefix);
  if (!ctx.ok || !ctx.context) {
    return { ok: false, context: "", sha, digest: "", messages: [], error: ctx.reason };
  }

  const slug = await ghRepoSlug(opts.rootDir);
  if (!slug) {
    return {
      ok: false,
      context: ctx.context,
      sha,
      digest: "",
      messages: [],
      error: "Could not resolve GitHub repo slug; is `gh` configured for this repo?",
    };
  }

  const report = await runChecks(opts.registry, opts.runConfig, undefined, {
    rootDir: opts.rootDir,
  });
  if (!report.ok) {
    return {
      ok: false,
      context: ctx.context,
      sha,
      digest: "",
      messages: [
        `attest aborted: ${summariseRunReport(report)}`,
        ...report.results.filter((r) => !r.ok).map((r) => `  ✗ ${r.id}`),
      ],
      error: "one or more checks failed",
      report,
    };
  }

  const digest = digestRun(sha, report.results);
  const prior = await readPriorAttestation(opts.rootDir, sha);
  const description = `${summariseRunReport(report)} · ${digest.slice(0, 12)}`;
  const post = await postCommitStatus(opts.rootDir, slug, sha, ctx.context, description);
  if (!post.ok) {
    return {
      ok: false,
      context: ctx.context,
      sha,
      digest,
      messages: [post.output.trim()],
      error: "GitHub status post failed",
      report,
    };
  }

  await writeAttestation(opts.rootDir, sha, ctx.context, digest);

  const replayNote = prior === digest ? "replay (cached digest)" : "fresh attestation";
  return {
    ok: true,
    context: ctx.context,
    sha,
    digest,
    messages: [`${ctx.context} → ${sha.slice(0, 12)} (${replayNote})`, `  ${description}`],
    report,
  };
}
