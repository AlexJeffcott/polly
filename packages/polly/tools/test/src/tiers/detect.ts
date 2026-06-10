/**
 * Host capability detection for need-gating.
 *
 * A case declaring `needs: ["docker"]` is skipped (not failed) when the host
 * can't satisfy it, unless `--strict-needs` is set. Detection is cached for the
 * lifetime of the process so a 30-case run probes `docker info` once.
 */
import type { Need } from "./types";

const cache = new Map<Need, boolean>();

async function commandSucceeds(argv: string[]): Promise<boolean> {
  try {
    const proc = Bun.spawn(argv, { stdout: "ignore", stderr: "ignore", stdin: "ignore" });
    return (await proc.exited) === 0;
  } catch {
    return false;
  }
}

async function probe(need: Need): Promise<boolean> {
  switch (need) {
    case "docker":
      // `docker info` fails fast when the daemon is down, unlike `docker --version`.
      return commandSucceeds(["docker", "info"]);
    case "browser":
      // Puppeteer ships Chromium as a devDependency; assume present in-repo.
      // A real probe would resolve the executable path, but that pulls puppeteer
      // into the engine. Front-ends that need a stricter check can override.
      return true;
    case "network":
      return true;
    default:
      return false;
  }
}

/** Resolve whether a need is satisfied, memoised. */
export async function hasNeed(need: Need): Promise<boolean> {
  const cached = cache.get(need);
  if (cached !== undefined) return cached;
  const result = await probe(need);
  cache.set(need, result);
  return result;
}

/** First unmet need among `needs`, or null if all are satisfied. */
export async function firstUnmetNeed(needs: Need[] | undefined): Promise<Need | null> {
  for (const need of needs ?? []) {
    if (!(await hasNeed(need))) return need;
  }
  return null;
}
