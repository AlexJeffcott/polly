/**
 * Type-aware mutant filter: a mutant the project's own TypeScript config
 * rejects is not a fault a developer could have shipped, so it is reported
 * `CompileError` and never run. Measured on polly's 44 targets before this
 * filter existed: 1,848 of 4,894 mutants (38 %) failed to type-check, among
 * them 323 of the 974 survivors — a third of the review queue.
 *
 * Mechanism: one `tsgo` process through TypeScript 7's `typescript/async`
 * API, with request file-system layers (`typescript/fs`) in place of disk
 * writes. The project is opened through a virtual
 * `tsconfig.polly-mutate.json` beside the nearest `tsconfig.json` that lists
 * the target; it extends that config and relaxes three options
 * (`TYPECHECK_OVERRIDES`), because a mutant routinely leaves a block
 * unreachable or a binding unused and neither is a type error. Each mutant is
 * then served as the target's text through a temporary snapshot layered on
 * the unmutated one, and only the target's own diagnostics are read: on
 * polly, checking every importer as well found no extra mutant in 4,894 and
 * cost 12 s of 57.
 *
 * The verdict is relative: a mutant is invalid when its error-category
 * diagnostics include one (by code and text) the unmutated file does not
 * have, so a project whose target already fails to type-check still gets a
 * filter, and never a false `CompileError`.
 *
 * `typescript-7` is the npm alias polly depends on (`npm:typescript@7.1.0-beta`,
 * exact), so a consumer's own `typescript` can stay on whatever version its
 * other tools need. The sync flavour of the API cannot run under Bun (it reads
 * `child.stdout._handle.fd`, which Bun's child process does not expose); the
 * async one can, and it batches the requests a tick issues into one message.
 */
import { existsSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import type { Diagnostic, Snapshot } from "typescript-7/async";
import { installCommand } from "../../../tool-deps/src/index.ts";
import { applyMutant } from "./generate.ts";
import type { Mutant } from "./types.ts";

type AsyncApi = typeof import("typescript-7/async");
type FsApi = typeof import("typescript-7/fs");
type Api = InstanceType<AsyncApi["API"]>;
type SnapshotParams = Parameters<Snapshot["update"]>[0];

/** Relaxed in the virtual config: mutants make code unreachable and bindings unused by design. */
export const TYPECHECK_OVERRIDES = {
  allowUnreachableCode: true,
  noUnusedLocals: false,
  noUnusedParameters: false,
};

export const TYPECHECK_CONFIG_NAME = "tsconfig.polly-mutate.json";

/** Caps a verdict's text, so a long assignability chain does not swamp the report. */
const REASON_LIMIT = 300;

export interface TypecheckTarget {
  /** Absolute, symlink-resolved. */
  file: string;
  mutants: readonly Mutant[];
}

export interface TypecheckOutcome {
  /** Mutant id → `TS<code>: <text>` of the first error the unmutated file does not have. */
  invalid: Map<string, string>;
  /** Targets the filter could not check, each with why. Their mutants run as usual. */
  skipped: { file: string; reason: string }[];
  /** Mutants that were checked (skipped targets excluded). */
  checked: number;
  wallMs: number;
}

export interface TypecheckOptions {
  /** For log lines: paths print relative to it. */
  cwd: string;
  log?: (line: string) => void;
}

interface Modules {
  api: AsyncApi;
  fs: FsApi;
}

/** The TypeScript 7 API modules, or null when `typescript-7` is not installed. */
async function loadApi(): Promise<Modules | null> {
  try {
    const [api, fs] = await Promise.all([import("typescript-7/async"), import("typescript-7/fs")]);
    return { api, fs };
  } catch {
    return null;
  }
}

/** `tsconfig.json` paths from the file's directory upward, nearest first. */
export function tsconfigCandidates(file: string): string[] {
  const out: string[] = [];
  let dir = dirname(file);
  for (;;) {
    const candidate = join(dir, "tsconfig.json");
    if (existsSync(candidate)) out.push(candidate);
    const parent = dirname(dir);
    if (parent === dir) return out;
    dir = parent;
  }
}

function virtualConfigFor(tsconfig: string): string {
  return join(dirname(tsconfig), TYPECHECK_CONFIG_NAME);
}

const VIRTUAL_CONFIG_TEXT = JSON.stringify({
  extends: "./tsconfig.json",
  compilerOptions: TYPECHECK_OVERRIDES,
});

function errorKeys(api: AsyncApi, diagnostics: readonly Diagnostic[]): string[] {
  return diagnostics
    .filter((d) => d.category === api.DiagnosticCategory.Error)
    .map((d) => `${d.code}|${d.text}`);
}

function reasonOf(key: string): string {
  const sep = key.indexOf("|");
  const text = key.slice(sep + 1).replace(/\s+/g, " ");
  const reason = `TS${key.slice(0, sep)}: ${text}`;
  return reason.length > REASON_LIMIT ? `${reason.slice(0, REASON_LIMIT - 1)}…` : reason;
}

/**
 * One tsgo session: the base snapshot (every virtual config opened so far,
 * every target unmutated) and the projects opened in it. Mutants never change
 * the base: each is checked in a temporary snapshot layered on it.
 */
class Session {
  private base: Snapshot | null = null;
  /** tsconfig.json → its virtual override config, or null when it could not be opened. */
  private readonly opened = new Map<string, string | null>();
  private readonly api: Api;

  constructor(
    private readonly mod: Modules,
    cwd: string
  ) {
    this.api = new mod.api.API({ cwd });
  }

  /** Opens `config` (served by a layer) in a new base snapshot. */
  private async open(config: string): Promise<Snapshot> {
    // A snapshot update builds its programs lazily; without `ensurePrograms`
    // the diagnostics come from the stale program and every mutant passes.
    const params: SnapshotParams = {
      openProjects: [config],
      fileSystem: this.mod.fs.createFileSystemLayer([[config, VIRTUAL_CONFIG_TEXT]]),
      ensurePrograms: true,
    };
    const next = this.base ? await this.base.update(params) : await this.api.createSnapshot(params);
    await this.base?.dispose();
    this.base = next;
    return next;
  }

  /** The virtual config of the nearest tsconfig.json whose program lists `file`, or null. */
  async projectFor(file: string): Promise<string | null> {
    for (const tsconfig of tsconfigCandidates(file)) {
      let config = this.opened.get(tsconfig);
      if (config === undefined) {
        config = virtualConfigFor(tsconfig);
        const snap = await this.open(config);
        if (!snap.getConfiguredProject(config)) config = null;
        this.opened.set(tsconfig, config);
      }
      if (config === null) continue;
      const project = this.base?.getConfiguredProject(config);
      if (project?.parsedCommandLine.fileNames.some((f) => samePath(f, file))) return config;
    }
    return null;
  }

  private async errorsIn(snapshot: Snapshot, config: string, file: string): Promise<string[]> {
    const program = snapshot.getConfiguredProject(config)?.program;
    if (!program) throw new Error(`polly mutate: tsgo lost the project ${config}`);
    const [syntactic, semantic] = await Promise.all([
      program.getSyntacticDiagnostics(file),
      program.getSemanticDiagnostics(file),
    ]);
    return [...errorKeys(this.mod.api, syntactic), ...errorKeys(this.mod.api, semantic)];
  }

  /** Verdicts for one target: mutant id → reason, for the mutants that add an error. */
  async check(config: string, target: TypecheckTarget, src: string): Promise<Map<string, string>> {
    const base = this.base;
    if (!base) throw new Error(`polly mutate: no snapshot for ${config}`);
    const invalid = new Map<string, string>();
    const baseline = new Set(await this.errorsIn(base, config, target.file));
    for (const m of target.mutants) {
      await this.api.runWithTemporaryFileUpdate(
        base,
        target.file,
        applyMutant(src, m),
        async (snap) => {
          const errors = await this.errorsIn(snap, config, target.file);
          const fresh = errors.find((k) => !baseline.has(k));
          if (fresh !== undefined) invalid.set(m.id, reasonOf(fresh));
        }
      );
    }
    return invalid;
  }

  async close(): Promise<void> {
    await this.api.close();
  }
}

function samePath(a: string, b: string): boolean {
  return a === b || a.toLowerCase() === b.toLowerCase();
}

/**
 * Type-check every mutant of every target. Null when `typescript-7` is not
 * installed (logged; the engine then runs every mutant).
 */
export async function typecheckMutants(
  targets: readonly TypecheckTarget[],
  opts: TypecheckOptions
): Promise<TypecheckOutcome | null> {
  const log = opts.log ?? (() => undefined);
  const started = performance.now();
  const outcome: TypecheckOutcome = { invalid: new Map(), skipped: [], checked: 0, wallMs: 0 };
  const withConfig = targets.filter((t) => {
    if (tsconfigCandidates(t.file).length > 0) return true;
    outcome.skipped.push({ file: t.file, reason: "no tsconfig.json above it" });
    return false;
  });
  if (withConfig.length === 0) {
    for (const s of outcome.skipped) log(`type filter: ${relative(opts.cwd, s.file)}: ${s.reason}`);
    outcome.wallMs = Math.round(performance.now() - started);
    return outcome;
  }
  const mod = await loadApi();
  if (!mod) {
    log(`type filter off: typescript-7 is not installed (${installCommand(["typescript-7"])})`);
    return null;
  }
  const session = new Session(mod, opts.cwd);
  try {
    for (const target of withConfig) {
      const config = await session.projectFor(target.file);
      if (!config) {
        outcome.skipped.push({ file: target.file, reason: "no tsconfig.json includes it" });
        continue;
      }
      const src = await Bun.file(target.file).text();
      const verdicts = await session.check(config, target, src);
      for (const [id, reason] of verdicts) outcome.invalid.set(id, reason);
      outcome.checked += target.mutants.length;
    }
  } finally {
    await session.close();
  }
  outcome.wallMs = Math.round(performance.now() - started);
  for (const s of outcome.skipped) log(`type filter: ${relative(opts.cwd, s.file)}: ${s.reason}`);
  log(
    `type filter: ${outcome.invalid.size} of ${outcome.checked} mutants fail to type-check ` +
      `(${(outcome.wallMs / 1000).toFixed(1)} s)`
  );
  return outcome;
}
