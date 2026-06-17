/**
 * Shared flag parsing for the tiered runner CLIs.
 *
 * Both front-ends (Polly's internal scripts/test/cli.ts and the consumer-facing
 * tools/test/src/tiers/cli.ts) accept the same flags; only their tier *sets*
 * differ. This keeps the surface identical.
 */

import type { CaseOrder } from "./types";

export interface TierArgs {
  /** Explicit tier names (positional or via --tier=a,b). */
  tiers: string[];
  /** --only=substr filters across tiers. */
  only: string[];
  all: boolean;
  full: boolean;
  list: boolean;
  bail: boolean;
  /** --fail-fast: soft early-stop on the first failing case. */
  failFast: boolean;
  /** --order=fast|cost|default within-tier ordering, or null to leave unset. */
  order: CaseOrder | null;
  strictNeeds: boolean;
  /** Path to write JSON results, or null. */
  json: string | null;
}

export const DEFAULT_JSON = "test-results/tiers.json";

const BOOL_FLAGS: Record<string, "all" | "full" | "list" | "bail" | "failFast" | "strictNeeds"> = {
  "--all": "all",
  "--full": "full",
  "--list": "list",
  "--bail": "bail",
  "--fail-fast": "failFast",
  "--strict-needs": "strictNeeds",
};

/** Narrow a raw `--order=` value to a {@link CaseOrder}, or null if unknown. */
function parseOrder(value: string): CaseOrder | null {
  if (value === "default" || value === "fast" || value === "cost") return value;
  return null;
}

function listValue(arg: string, name: string): string[] {
  return arg.startsWith(name) ? arg.slice(name.length).split(",") : [];
}

/** Apply a value-bearing flag (`--name=value`, or bare `--json`). Returns false
 * if `arg` isn't one, so the caller can fall through to tier names. Exits(2) on
 * a malformed `--order=`. */
function applyValueFlag(args: TierArgs, arg: string): boolean {
  if (arg === "--json") {
    args.json = DEFAULT_JSON;
    return true;
  }
  if (arg.startsWith("--json=")) {
    args.json = arg.slice("--json=".length);
    return true;
  }
  if (arg.startsWith("--tier=")) {
    args.tiers.push(...listValue(arg, "--tier="));
    return true;
  }
  if (arg.startsWith("--only=")) {
    args.only.push(...listValue(arg, "--only="));
    return true;
  }
  if (arg.startsWith("--order=")) {
    const order = parseOrder(arg.slice("--order=".length));
    if (order === null) {
      console.log("Unknown --order value (expected default, fast, or cost)");
      process.exit(2);
    }
    args.order = order;
    return true;
  }
  return false;
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
    failFast: false,
    order: null,
    strictNeeds: false,
    json: null,
  };
  for (const arg of argv) {
    const boolKey = BOOL_FLAGS[arg];
    if (boolKey) {
      args[boolKey] = true;
      continue;
    }
    if (applyValueFlag(args, arg)) {
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
