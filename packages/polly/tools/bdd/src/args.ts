/**
 * Argument parsing for `polly bdd`. Flat verb dispatcher, mirroring the shape
 * of `tools/mutate/src/args.ts`.
 */
export interface BddArgs {
  /** First positional: "run" | "check" | "new" (default "run"). */
  verb: string;
  /** Positionals after the verb (e.g. a feature path, or a new feature name). */
  rest: string[];
  /** --features <glob> override. */
  features?: string;
  /** --steps <glob> override. */
  steps?: string;
  /** --tags <expr> filter (plain tag name, optionally prefixed ~ to negate). */
  tags?: string;
  /** --json machine-readable output. */
  json: boolean;
  /** -h / --help. */
  help: boolean;
}

const VALUE_FLAGS = new Set(["--features", "--steps", "--tags"]);

export function parseBddArgs(argv: string[]): BddArgs {
  const positionals: string[] = [];
  const flags = new Map<string, string>();
  const bools = new Set<string>();

  let i = 0;
  while (i < argv.length) {
    const a = argv[i] ?? "";
    if (VALUE_FLAGS.has(a)) {
      flags.set(a, argv[i + 1] ?? "");
      i += 2;
    } else {
      if (a.startsWith("-")) bools.add(a);
      else positionals.push(a);
      i += 1;
    }
  }

  return {
    verb: positionals[0] ?? "run",
    rest: positionals.slice(1),
    features: flags.get("--features"),
    steps: flags.get("--steps"),
    tags: flags.get("--tags"),
    json: bools.has("--json"),
    help: bools.has("--help") || bools.has("-h"),
  };
}
