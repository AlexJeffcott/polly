/**
 * Secret-scanning conformance checks.
 *
 * Two paired checks that protect a repository from accidentally
 * committing credentials:
 *
 *   - `checkSecrets` spawns `gitleaks detect` against the working
 *     tree and returns the exit code + stdout. Consumers are
 *     expected to have `gitleaks` on PATH (via `brew install
 *     gitleaks` or equivalent); the check reports a clear failure
 *     when the binary is missing.
 *
 *   - `checkGitignoreCoversAllowlist` parses a `.gitleaks.toml`
 *     config, pulls out the path patterns that sit in an allowlist
 *     *section* marked as "gitignored files" (via comment
 *     markers), and verifies each one is actually covered by
 *     `.gitignore`. This catches the footgun where a repo
 *     allowlists `.env` in gitleaks config but forgets to add it
 *     to `.gitignore`, so the allowlist entry silently lets a real
 *     secret slip through.
 *
 * Adapted from the devctl `check` command in the Lingua project.
 *
 * @example
 * ```typescript
 * import {
 *   checkSecrets,
 *   checkGitignoreCoversAllowlist,
 * } from "@fairfox/polly/quality";
 *
 * const scan = await checkSecrets({ root: process.cwd() });
 * if (scan.exitCode !== 0) process.exit(scan.exitCode);
 *
 * const cover = await checkGitignoreCoversAllowlist({
 *   root: process.cwd(),
 * });
 * if (cover.missing.length > 0) {
 *   cover.print();
 *   process.exit(1);
 * }
 * ```
 */

import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { logger } from "./logger";

const defaultWrite = (msg: string): void => logger.error(msg);

export interface CheckSecretsOptions {
  /** Repository root to scan. */
  root: string;
  /** Path to a gitleaks TOML config, relative to `root`. Defaults
   * to `.gitleaks.toml`. */
  configPath?: string;
  /** Scan the working tree (`--no-git`) or the git history.
   * Defaults to true (working tree only — faster, and what most
   * pre-commit / CI flows want). */
  noGit?: boolean;
}

export interface SecretsCheckResult {
  /** Whether `gitleaks` was found on PATH at all. */
  binaryFound: boolean;
  /** `gitleaks detect` exit code, or null when the binary was
   * missing. 0 = clean, 1 = secrets found, other = gitleaks
   * error. */
  exitCode: number | null;
  /** Streamed gitleaks stdout + stderr. Empty when the scan was
   * skipped. */
  output: string;
  print: (write?: (msg: string) => void) => void;
}

/**
 * Run gitleaks against the working tree. Returns `binaryFound:
 * false` if the binary isn't on PATH — callers typically treat
 * that as a hard failure with an install hint.
 */
export async function checkSecrets(options: CheckSecretsOptions): Promise<SecretsCheckResult> {
  const which = Bun.spawn(["which", "gitleaks"], {
    stdout: "ignore",
    stderr: "ignore",
  });
  await which.exited;
  if (which.exitCode !== 0) {
    return {
      binaryFound: false,
      exitCode: null,
      output: "",
      print: (write = defaultWrite) => {
        write(
          "gitleaks is not on PATH. Install with `brew install gitleaks` (macOS) or from https://github.com/gitleaks/gitleaks/releases."
        );
      },
    };
  }

  const args = ["gitleaks", "detect", "--source", options.root ?? "."];
  if (options.noGit !== false) {
    args.push("--no-git");
  }
  if (options.configPath) {
    args.push("-c", options.configPath);
  }

  const proc = Bun.spawn(args, {
    cwd: options.root,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [stdout, stderr] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  const output = `${stdout}${stderr}`;
  return {
    binaryFound: true,
    exitCode: proc.exitCode,
    output,
    print: (write = defaultWrite) => {
      if (output) {
        write(output);
      }
    },
  };
}

export interface CheckGitignoreOptions {
  /** Repository root. */
  root: string;
  /** Path to the gitleaks TOML config, relative to `root`. Defaults
   * to `.gitleaks.toml`. */
  tomlPath?: string;
  /** Path to the gitignore file, relative to `root`. Defaults to
   * `.gitignore`. */
  gitignorePath?: string;
  /** Strings that, when seen in a comment line of the TOML, mark
   * the start of a "must be gitignored" section. Defaults cover
   * "Gitignored files" and "Local dev TLS certs". */
  sectionStartMarkers?: string[];
  /** Strings that close a must-be-gitignored section. Defaults to
   * "Test fixtures" so the common lingua-style layout works
   * unchanged. */
  sectionEndMarkers?: string[];
}

export interface GitignoreCheckResult {
  /** TOML-listed allowlisted paths that `.gitignore` does NOT
   * cover. Each string is the derived plain filename (e.g.
   * `.env`, `certs/key.pem`). */
  missing: string[];
  /** All paths the TOML required to be gitignored, whether or not
   * .gitignore covers them. Useful for audits. */
  required: string[];
  print: (write?: (msg: string) => void) => void;
}

/**
 * Parse a gitleaks TOML config and verify every allowlisted path
 * that the config marks as "this file should be gitignored" is in
 * fact present in `.gitignore`. Returns the list of allowlisted
 * paths that are NOT gitignored.
 *
 * The check trusts section markers in the TOML comments to decide
 * which allowlist entries apply. By default:
 *
 *   - "Gitignored files" and "Local dev TLS certs" open a
 *     must-be-gitignored section.
 *   - "Test fixtures" closes it.
 *
 * Entries outside those sections (e.g. test-fixture paths) are
 * ignored by this check.
 */
function parseRequiredPaths(toml: string, starts: string[], ends: string[]): string[] {
  const required: string[] = [];
  let inSection = false;
  for (const line of toml.split("\n")) {
    if (starts.some((m) => line.includes(m))) {
      inSection = true;
      continue;
    }
    if (ends.some((m) => line.includes(m))) {
      inSection = false;
      continue;
    }
    if (!inSection) {
      continue;
    }
    const match = line.match(/'''(.+?)'''/);
    if (!match?.[1]) {
      continue;
    }
    // Convert gitleaks regex to plain filename (strip backslash
    // escapes and trailing anchors) for a gitignore-style lookup.
    required.push(match[1].replace(/\\\./g, ".").replace(/\$$/, ""));
  }
  return required;
}

function gitignoreLineCovers(giLine: string, filename: string): boolean {
  if (!giLine || giLine.startsWith("#")) {
    return false;
  }
  if (giLine === filename) {
    return true;
  }
  const dirMatch = giLine.match(/^\*?\*?\/?(.+)\/$/);
  if (dirMatch?.[1] && filename.startsWith(dirMatch[1])) {
    return true;
  }
  if (giLine.endsWith("/") && filename.startsWith(giLine)) {
    return true;
  }
  return false;
}

const emptyGitignoreResult: GitignoreCheckResult = {
  missing: [],
  required: [],
  print: () => {
    // No TOML means nothing to enforce; callers typically treat
    // this as "skipped" and print their own hint. Leaving the
    // printer a no-op keeps the API uniform without emitting
    // spurious output.
  },
};

export async function checkGitignoreCoversAllowlist(
  options: CheckGitignoreOptions
): Promise<GitignoreCheckResult> {
  const tomlPath = join(options.root, options.tomlPath ?? ".gitleaks.toml");
  const gitignorePath = join(options.root, options.gitignorePath ?? ".gitignore");
  const starts = options.sectionStartMarkers ?? ["Gitignored files", "Local dev TLS certs"];
  const ends = options.sectionEndMarkers ?? ["Test fixtures"];

  let toml: string;
  try {
    toml = await readFile(tomlPath, "utf8");
  } catch {
    return emptyGitignoreResult;
  }
  let gitignore: string;
  try {
    gitignore = await readFile(gitignorePath, "utf8");
  } catch {
    gitignore = "";
  }

  const required = parseRequiredPaths(toml, starts, ends);
  const gitignoreLines = gitignore.split("\n").map((l) => l.trim());
  const missing = required.filter(
    (filename) => !gitignoreLines.some((gi) => gitignoreLineCovers(gi, filename))
  );

  return {
    missing,
    required,
    print: (write = defaultWrite) => {
      if (missing.length === 0) {
        return;
      }
      write("Paths allowed by .gitleaks.toml are NOT covered by .gitignore:");
      for (const f of missing) {
        write(`  ${f}`);
      }
      write(
        "These files may contain secrets. Add them to .gitignore so the allowlist entry doesn't become a hiding place."
      );
    },
  };
}
