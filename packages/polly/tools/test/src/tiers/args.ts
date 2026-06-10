/**
 * Shared flag parsing for the tiered runner CLIs.
 *
 * Both front-ends (Polly's internal scripts/test/cli.ts and the consumer-facing
 * tools/test/src/tiers/cli.ts) accept the same flags; only their tier *sets*
 * differ. This keeps the surface identical.
 */

export interface TierArgs {
  /** Explicit tier names (positional or via --tier=a,b). */
  tiers: string[];
  /** --only=substr filters across tiers. */
  only: string[];
  all: boolean;
  full: boolean;
  list: boolean;
  bail: boolean;
  strictNeeds: boolean;
  /** Path to write JSON results, or null. */
  json: string | null;
}

export const DEFAULT_JSON = "test-results/tiers.json";

const BOOL_FLAGS: Record<string, "all" | "full" | "list" | "bail" | "strictNeeds"> = {
  "--all": "all",
  "--full": "full",
  "--list": "list",
  "--bail": "bail",
  "--strict-needs": "strictNeeds",
};

function listValue(arg: string, name: string): string[] {
  return arg.startsWith(name) ? arg.slice(name.length).split(",") : [];
}

/** Parse argv into {@link TierArgs}. Exits(2) on an unknown `--flag`. */
export function parseTierArgs(argv: string[]): TierArgs {
  const args: TierArgs = {
    tiers: [],
    only: [],
    all: false,
    full: false,
    list: false,
    bail: false,
    strictNeeds: false,
    json: null,
  };
  for (const arg of argv) {
    const boolKey = BOOL_FLAGS[arg];
    if (boolKey) {
      args[boolKey] = true;
      continue;
    }
    if (arg === "--json") {
      args.json = DEFAULT_JSON;
      continue;
    }
    if (arg.startsWith("--json=")) {
      args.json = arg.slice("--json=".length);
      continue;
    }
    if (arg.startsWith("--tier=")) {
      args.tiers.push(...listValue(arg, "--tier="));
      continue;
    }
    if (arg.startsWith("--only=")) {
      args.only.push(...listValue(arg, "--only="));
      continue;
    }
    if (arg.startsWith("-")) {
      console.log(`Unknown flag: ${arg}`);
      process.exit(2);
    }
    args.tiers.push(arg);
  }
  return args;
}
