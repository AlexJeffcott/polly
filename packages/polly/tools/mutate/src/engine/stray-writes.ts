/**
 * Stray-write detection. Mutant runs share the project's working tree (no
 * sandbox copy), so a mutant that redirects a write — a storage path, a temp
 * dir — leaves a file in the repo. Polly's own storage-adapter.ts did exactly
 * this (`st/orage-adapter-id` in the repo root after every full run).
 *
 * The engine snapshots `git status` before the run, after the baselines and
 * after the mutants, and reports each new entry. It never deletes: a path that
 * is new to git may still be the user's own work in progress.
 *
 * Untracked files are listed one by one (`--untracked-files=all`), so a new
 * file inside an already-untracked directory still shows. Ignored paths are
 * listed as their matching pattern (`--ignored=matching`): a write to a new
 * `*.log` shows, a write inside an existing `node_modules/` does not.
 */
export interface WorktreeSnapshot {
  /** Absolute repo root; entry paths are relative to it. */
  root: string;
  /** `XY path` lines, so a clean → modified change counts as new. */
  entries: Set<string>;
}

function git(cwd: string, args: string[]): string | null {
  const proc = Bun.spawnSync(["git", "-C", cwd, ...args], { stdout: "pipe", stderr: "ignore" });
  return proc.exitCode === 0 ? proc.stdout.toString() : null;
}

/** Null when `cwd` is not inside a git worktree (or git is not installed). */
export function snapshotWorktree(cwd: string): WorktreeSnapshot | null {
  const root = git(cwd, ["rev-parse", "--show-toplevel"])?.trim();
  if (!root) return null;
  const out = git(root, [
    "status",
    "--porcelain=v1",
    "-z",
    "--untracked-files=all",
    "--ignored=matching",
  ]);
  if (out === null) return null;
  const entries = new Set<string>();
  const tokens = out.split("\0");
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    if (!token) continue;
    entries.add(token);
    // A rename or copy is followed by its source path as a separate token.
    if (token[0] === "R" || token[0] === "C") i++;
  }
  return { root, entries };
}

/** Paths (relative to the repo root) whose `git status` entry is in `after` but not `before`. */
export function newPaths(
  before: WorktreeSnapshot | null,
  after: WorktreeSnapshot | null
): string[] {
  if (!before || !after || before.root !== after.root) return [];
  const paths = new Set<string>();
  for (const entry of after.entries) if (!before.entries.has(entry)) paths.add(entry.slice(3));
  return [...paths].sort();
}
