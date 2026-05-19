/**
 * Plugin host for `@fairfox/polly/quality`.
 *
 * Loads plugins, validates check ids and per-check config, and runs
 * checks in parallel against a `rootDir`. Each check goes through the
 * cache layer first: a content-hash hit returns the prior outcome
 * without invoking the body; a miss runs and persists the result.
 *
 * Errors thrown inside a check are caught and reported as a failed
 * `CheckRunResult` so one broken plugin does not abort the whole run.
 */

import { computeInputsHash, getCachedOutcome, setCachedOutcome } from "./cache";
import type {
  Check,
  CheckOutcome,
  CheckRunResult,
  QualityPlugin,
  QualityRunConfig,
  RunReport,
} from "./types";

export type RegisteredCheck = {
  check: Check<unknown>;
  plugin: QualityPlugin;
};

/**
 * Build a flat id-keyed registry from the configured plugins. Throws on
 * plugin name collision or check id collision (within or across
 * plugins) so misconfiguration fails at load time, not at run time.
 */
export function registerPlugins(plugins: QualityPlugin[]): Map<string, RegisteredCheck> {
  const registry = new Map<string, RegisteredCheck>();
  const pluginNames = new Set<string>();
  for (const plugin of plugins) {
    if (pluginNames.has(plugin.name)) {
      throw new Error(`Quality plugin name collision: "${plugin.name}" registered twice`);
    }
    pluginNames.add(plugin.name);
    for (const check of plugin.checks) {
      if (!check.id.startsWith(`${plugin.name}:`)) {
        throw new Error(
          `Check "${check.id}" is registered under plugin "${plugin.name}" but its id does not begin with "${plugin.name}:"`
        );
      }
      if (registry.has(check.id)) {
        const prior = registry.get(check.id)?.plugin.name ?? "<unknown>";
        throw new Error(
          `Check id collision: "${check.id}" registered by plugins "${prior}" and "${plugin.name}"`
        );
      }
      registry.set(check.id, { check, plugin });
    }
  }
  return registry;
}

/**
 * Validate that every per-check config block in the run config is
 * accepted by the corresponding check's `validate` function. Surfaces all
 * errors at once rather than aborting on the first.
 */
export function validateRunConfig(
  registry: Map<string, RegisteredCheck>,
  runConfig: QualityRunConfig
): string[] {
  const errors: string[] = [];
  const checks = runConfig.checks ?? {};
  for (const [id, cfg] of Object.entries(checks)) {
    const entry = registry.get(id);
    if (!entry) {
      errors.push(`Configuration references unknown check id "${id}"`);
      continue;
    }
    if (!entry.check.validate) continue;
    const result = entry.check.validate(cfg);
    if (result === null) continue;
    for (const msg of result) {
      errors.push(`[${id}] ${msg}`);
    }
  }
  return errors;
}

export type RunOptions = {
  rootDir: string;
  /** When set, skip cache reads and writes. */
  noCache?: boolean;
  /** Concurrency cap; defaults to the number of registered checks. */
  concurrency?: number;
  signal?: AbortSignal;
};

async function resolveCacheHash(
  check: Check<unknown>,
  config: unknown,
  opts: RunOptions
): Promise<string | null> {
  if (opts.noCache || !check.filesRead) return null;
  try {
    const files = await check.filesRead(config, opts.rootDir);
    const extras = check.cacheKeyExtras?.(config);
    return computeInputsHash({ files, ...(extras ? { extras } : {}) }, opts.rootDir);
  } catch {
    // Cache-input collection failures fall through to a non-cached run.
    return null;
  }
}

async function executeBody(
  check: Check<unknown>,
  config: unknown,
  opts: RunOptions
): Promise<CheckOutcome | { error: string }> {
  try {
    return await check.run({
      rootDir: opts.rootDir,
      config,
      ...(opts.signal ? { signal: opts.signal } : {}),
    });
  } catch (err) {
    return { error: err instanceof Error ? err.message : String(err) };
  }
}

async function runOne(
  entry: RegisteredCheck,
  config: unknown,
  opts: RunOptions
): Promise<CheckRunResult> {
  const { check } = entry;
  const start = Date.now();

  const cacheHash = await resolveCacheHash(check, config, opts);
  if (cacheHash) {
    const cached = await getCachedOutcome(opts.rootDir, check.id, cacheHash);
    if (cached) {
      return {
        id: check.id,
        ok: cached.ok,
        durationMs: Date.now() - start,
        cached: true,
        messages: cached.messages,
      };
    }
  }

  const result = await executeBody(check, config, opts);
  if ("error" in result) {
    return {
      id: check.id,
      ok: false,
      durationMs: Date.now() - start,
      cached: false,
      messages: [],
      error: result.error,
    };
  }

  if (cacheHash && result.ok) {
    // Only cache passing outcomes — a cached failure could mask a fix
    // until the next input change, which is surprising in CI.
    try {
      await setCachedOutcome(opts.rootDir, check.id, cacheHash, result);
    } catch {
      // Cache-write failures are non-fatal; the next run just re-executes.
    }
  }

  return {
    id: check.id,
    ok: result.ok,
    durationMs: Date.now() - start,
    cached: false,
    messages: result.messages,
  };
}

async function runWithConcurrency<T, R>(
  items: T[],
  limit: number,
  worker: (item: T) => Promise<R>
): Promise<R[]> {
  if (items.length === 0) return [];
  const results: R[] = new Array(items.length);
  let cursor = 0;
  const workers = Array.from({ length: Math.max(1, Math.min(limit, items.length)) }, async () => {
    while (true) {
      const i = cursor++;
      if (i >= items.length) return;
      const item = items[i];
      if (item === undefined) return;
      results[i] = await worker(item);
    }
  });
  await Promise.all(workers);
  return results;
}

/**
 * Run a set of checks. If `ids` is undefined, runs every registered check.
 * Returns a `RunReport` with per-check results plus an aggregate `ok`.
 */
export async function runChecks(
  registry: Map<string, RegisteredCheck>,
  runConfig: QualityRunConfig,
  ids: string[] | undefined,
  opts: RunOptions
): Promise<RunReport> {
  const start = Date.now();
  const targets: RegisteredCheck[] = [];
  if (ids === undefined) {
    targets.push(...registry.values());
  } else {
    for (const id of ids) {
      const entry = registry.get(id);
      if (!entry) {
        throw new Error(`Unknown check id: "${id}"`);
      }
      targets.push(entry);
    }
  }

  const checks = runConfig.checks ?? {};
  const limit = opts.concurrency ?? targets.length;
  const results = await runWithConcurrency(targets, limit, (entry) =>
    runOne(entry, checks[entry.check.id], opts)
  );

  return {
    ok: results.every((r) => r.ok),
    results,
    totalDurationMs: Date.now() - start,
  };
}

export function listChecks(registry: Map<string, RegisteredCheck>): Array<{
  id: string;
  description: string;
  plugin: string;
}> {
  return Array.from(registry.values())
    .map(({ check, plugin }) => ({
      id: check.id,
      description: check.description,
      plugin: plugin.name,
    }))
    .sort((a, b) => a.id.localeCompare(b.id));
}
