/**
 * Argument parsing for `polly mutate`. Hand-rolled (matching the rest of the
 * polly CLI), with the value-flag / bool-flag split that lets a flag value
 * (`--report path.json`) not be mistaken for a positional verb.
 */

export interface MutateArgs {
  /** First positional: "run" (default when bare) | "report" | "decisions" | "verify" | an unknown token to error on. */
  verb: string;
  /** Positionals after the verb (e.g. ["decide", file, verdict, ...rationale] for `decisions decide …`). */
  rest: string[];
  config?: string;
  report?: string;
  decisions?: string;
  db?: string;
  noReport: boolean;
  /** `verify --run` (run a fresh Stryker pass before checking the contract). */
  run: boolean;
  /** `init --force` (overwrite an existing stryker.conf.json). */
  force: boolean;
  help: boolean;
}

const KNOWN_VERBS = new Set(["run", "report", "decisions", "verify", "init", "help"]);
const VALUE_FLAGS = new Set(["--config", "--report", "--decisions", "--db"]);

export function parseMutateArgs(argv: string[]): MutateArgs {
  const positionals: string[] = [];
  const flags = new Map<string, string>();
  const bools = new Set<string>();

  let i = 0;
  while (i < argv.length) {
    const a = argv[i];
    if (a === undefined) break;
    if (VALUE_FLAGS.has(a)) {
      flags.set(a, argv[i + 1] ?? "");
      i += 2;
    } else {
      if (a.startsWith("-")) bools.add(a);
      else positionals.push(a);
      i += 1;
    }
  }

  const verbRaw = positionals[0];
  const help = bools.has("--help") || bools.has("-h") || verbRaw === "help";
  const verb = verbRaw === undefined ? "run" : KNOWN_VERBS.has(verbRaw) ? verbRaw : verbRaw;

  return {
    verb,
    rest: positionals.slice(1),
    config: flags.get("--config"),
    report: flags.get("--report"),
    decisions: flags.get("--decisions"),
    db: flags.get("--db"),
    noReport: bools.has("--no-report"),
    run: bools.has("--run"),
    force: bools.has("--force"),
    help,
  };
}
