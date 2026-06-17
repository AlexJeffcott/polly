/**
 * The tiered test engine.
 *
 * Runs a {@link TierPlan} tier-by-tier in order. Within a tier, cases run with
 * bounded concurrency. Each case is its own subprocess (see worker.ts) so the
 * isolation the e2e scripts assume is preserved. Cases whose host needs are
 * unmet are skipped (logged), not failed, unless `strictNeeds` is set.
 */
import { firstUnmetNeed } from "./detect";
import { orderCases } from "./order";
import { SENTINEL } from "./protocol";
import type {
  CaseOutcome,
  CaseReport,
  CaseSpec,
  EngineOptions,
  RunReport,
  Tier,
  TierPlan,
} from "./types";

const DEFAULT_TIMEOUT_MS = 120_000;

async function workerPath(): Promise<string> {
  const bundled = `${import.meta.dir}/worker.js`;
  const source = `${import.meta.dir}/worker.ts`;
  return (await Bun.file(bundled).exists()) ? bundled : source;
}

function caseLabel(spec: CaseSpec): string {
  return spec.label ?? spec.id;
}

function caseMatches(spec: CaseSpec, only: string[] | undefined): boolean {
  if (!only || only.length === 0) return true;
  const haystacks = [spec.id, caseLabel(spec), ...(spec.tags ?? [])].map((s) => s.toLowerCase());
  return only.some((needle) => {
    const n = needle.toLowerCase();
    return haystacks.some((h) => h.includes(n));
  });
}

interface SubprocOutcome {
  exitCode: number;
  stdout: string;
  timedOut: boolean;
}

async function runSubprocess(
  argv: string[],
  opts: { cwd?: string; env: Record<string, string | undefined>; timeoutMs: number },
  onLine: (line: string) => void
): Promise<SubprocOutcome> {
  const proc = Bun.spawn(argv, {
    cwd: opts.cwd,
    env: opts.env,
    stdout: "pipe",
    stderr: "pipe",
    stdin: "ignore",
  });

  let timedOut = false;
  const timer = setTimeout(() => {
    timedOut = true;
    proc.kill();
  }, opts.timeoutMs);

  const chunks: string[] = [];
  const pump = async (stream: ReadableStream<Uint8Array>): Promise<void> => {
    const decoder = new TextDecoder();
    let buffered = "";
    for await (const chunk of stream) {
      buffered += decoder.decode(chunk, { stream: true });
      let nl = buffered.indexOf("\n");
      while (nl !== -1) {
        const line = buffered.slice(0, nl);
        chunks.push(line);
        onLine(line);
        buffered = buffered.slice(nl + 1);
        nl = buffered.indexOf("\n");
      }
    }
    if (buffered) {
      chunks.push(buffered);
      onLine(buffered);
    }
  };

  await Promise.all([pump(proc.stdout), pump(proc.stderr)]);
  const exitCode = await proc.exited;
  clearTimeout(timer);

  return { exitCode, stdout: chunks.join("\n"), timedOut };
}

function parseSentinel(stdout: string): { pass: boolean; message?: string } | null {
  const idx = stdout.lastIndexOf(SENTINEL);
  if (idx === -1) return null;
  const after = stdout.slice(idx + SENTINEL.length);
  const newline = after.indexOf("\n");
  const json = newline === -1 ? after : after.slice(0, newline);
  try {
    const parsed = JSON.parse(json.trim());
    return { pass: Boolean(parsed.pass), message: parsed.message };
  } catch {
    return null;
  }
}

interface Verdict {
  outcome: CaseOutcome;
  message?: string;
}

const VERDICT_ICON: Record<CaseOutcome, string> = {
  pass: "✓",
  fail: "✗",
  skip: "⊘",
  timeout: "⏱",
};

/** Resolve argv + cwd for a case, falling back to the run-wide cwd. */
function buildInvocation(
  spec: CaseSpec,
  worker: string,
  options: EngineOptions
): { argv: string[]; cwd?: string } {
  if (spec.exec.kind === "module") {
    return { argv: ["bun", worker, spec.exec.modulePath, spec.id], cwd: options.cwd };
  }
  return { argv: spec.exec.argv, cwd: spec.exec.cwd ?? options.cwd };
}

/** Decide pass/fail/timeout, preferring the sentinel over the exit code. */
function decideVerdict(spec: CaseSpec, result: SubprocOutcome, timeoutMs: number): Verdict {
  if (result.timedOut) return { outcome: "timeout", message: `timed out after ${timeoutMs}ms` };
  const sentinel = spec.exec.kind === "module" ? parseSentinel(result.stdout) : null;
  const pass = sentinel ? sentinel.pass : result.exitCode === 0;
  if (pass) return { outcome: "pass" };
  return { outcome: "fail", message: sentinel?.message ?? `exit code ${result.exitCode}` };
}

async function runOneCase(
  spec: CaseSpec,
  tier: Tier,
  options: EngineOptions,
  worker: string
): Promise<CaseReport> {
  const label = caseLabel(spec);
  const log = options.log ?? ((m: string) => console.log(m));

  const unmet = await firstUnmetNeed(spec.needs);
  if (unmet && !options.strictNeeds) {
    log(`  ⊘ ${label} — skipped (needs ${unmet})`);
    return {
      tier: tier.name,
      id: spec.id,
      label,
      outcome: "skip",
      durationMs: 0,
      skipReason: `needs ${unmet}`,
    };
  }

  const timeoutMs = spec.timeoutMs ?? tier.timeoutMs ?? DEFAULT_TIMEOUT_MS;
  const env: Record<string, string | undefined> = { ...process.env, ...options.env };
  const { argv, cwd } = buildInvocation(spec, worker, options);

  const started = performance.now();
  const prefix = `    [${spec.id}] `;
  const result = await runSubprocess(argv, { cwd, env, timeoutMs }, (line) => {
    if (!line.includes(SENTINEL) && line.trim()) log(prefix + line);
  });
  const durationMs = Math.round(performance.now() - started);

  const verdict = decideVerdict(spec, result, timeoutMs);
  const tail = verdict.message ? ` — ${verdict.message}` : "";
  log(`  ${VERDICT_ICON[verdict.outcome]} ${label} (${durationMs}ms)${tail}`);
  return {
    tier: tier.name,
    id: spec.id,
    label,
    outcome: verdict.outcome,
    durationMs,
    message: verdict.message,
  };
}

async function runTier(tier: Tier, options: EngineOptions, worker: string): Promise<CaseReport[]> {
  const log = options.log ?? ((m: string) => console.log(m));
  const matched = tier.cases.filter((c) => caseMatches(c, options.only));
  if (matched.length === 0) return [];
  const selected = orderCases(matched, options.order ?? "default");

  log(
    `\n▶ ${tier.name}${tier.description ? ` — ${tier.description}` : ""} (${selected.length} case${selected.length === 1 ? "" : "s"})`
  );

  const concurrency = Math.max(1, tier.concurrency ?? 1);
  const failFast = options.failFast ?? false;
  // Slots left empty when soft-fail-fast aborts before claiming them; filtered out below.
  const reports: (CaseReport | undefined)[] = new Array(selected.length);
  let next = 0;
  let aborted = false;
  async function worker_loop(): Promise<void> {
    while (!aborted) {
      const i = next++;
      const spec = selected[i];
      if (!spec) return;
      const report = await runOneCase(spec, tier, options, worker);
      reports[i] = report;
      if (failFast && (report.outcome === "fail" || report.outcome === "timeout")) {
        aborted = true; // soft: in-flight siblings finish, but no new case is claimed
      }
    }
  }
  await Promise.all(Array.from({ length: Math.min(concurrency, selected.length) }, worker_loop));
  const done = reports.filter((r): r is CaseReport => r !== undefined);
  if (aborted && done.length < selected.length) {
    log(
      `  ⏹ fail-fast: stopped after a failure — ${selected.length - done.length} case(s) not run`
    );
  }
  return done;
}

/** Run a plan and return a structured report. Does not exit the process. */
export async function runPlan(plan: TierPlan, options: EngineOptions = {}): Promise<RunReport> {
  const log = options.log ?? ((m: string) => console.log(m));
  const worker = await workerPath();
  const wanted = options.tiers && options.tiers.length > 0 ? new Set(options.tiers) : null;

  const started = performance.now();
  const stopOnFail = Boolean(options.bail || options.failFast);
  const all: CaseReport[] = [];
  for (const tier of plan.tiers) {
    if (wanted && !wanted.has(tier.name)) continue;
    const reports = await runTier(tier, options, worker);
    all.push(...reports);
    if (stopOnFail && reports.some((r) => r.outcome === "fail" || r.outcome === "timeout")) {
      log(
        `\n⏹ ${options.failFast ? "fail-fast" : "bail"}: stopping after failing tier "${tier.name}"`
      );
      break;
    }
  }

  const durationMs = Math.round(performance.now() - started);
  const passed = all.filter((r) => r.outcome === "pass").length;
  const failed = all.filter((r) => r.outcome === "fail" || r.outcome === "timeout").length;
  const skipped = all.filter((r) => r.outcome === "skip").length;
  return { cases: all, passed, failed, skipped, durationMs, ok: failed === 0 };
}
