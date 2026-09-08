// Memory ceilings for a TLC run (polly#181).
//
// Without a cap, `docker run` gets no `--memory` and the JVM gets no `-Xmx`, so
// TLC sizes its heap from `MaxRAMPercentage` (25%) of whatever Docker Desktop
// was allocated. That is a machine setting: the same spec on the same polly
// version chose 1984MB on one allocation and 6000MB on another, and a long run
// died mid-check with no TLC message at all — the host's low-memory handling
// killed it. A model too large for the ceiling should end with a TLC message
// naming the run, not a silent kill the user has to infer from `docker info`.

/**
 * Container memory ceiling when `verification.memory` is unset.
 *
 * Fixed rather than a fraction of the host, so two machines with different
 * Docker Desktop allocations run the same model with the same heap and get the
 * same answer.
 */
export const DEFAULT_TLC_MEMORY = "4g";

/**
 * Floor for `verification.memory`. Below this the JVM spends its whole heap on
 * TLC's own fingerprint set and the run cannot make progress, so it is rejected
 * at config validation rather than started.
 */
export const MIN_TLC_MEMORY = "512m";

/**
 * Fraction of the container limit given to the JVM heap.
 *
 * The rest is the JVM's non-heap use — TLC's off-heap fingerprint set (it
 * reports `64MB offheap`), metaspace, thread stacks and the JVM itself. Keeping
 * `-Xmx` under the cgroup limit means the JVM throws OutOfMemoryError, which
 * TLC prints, instead of the kernel killing the container silently.
 */
export const JVM_HEAP_FRACTION = 0.75;

const MEGABYTE = 1024 ** 2;

const UNIT_BYTES: Record<string, number> = {
  b: 1,
  k: 1024,
  m: MEGABYTE,
  g: 1024 ** 3,
};

/**
 * Bytes for a docker-style memory string (`"512m"`, `"8g"`, `"1073741824"`).
 * `null` when the string is not one — the caller reports it, never guesses.
 */
export function parseMemoryBytes(spec: string): number | null {
  const match = /^(\d+)\s*([bkmg])?$/i.exec(spec.trim());
  if (!match?.[1]) return null;

  const value = Number.parseInt(match[1], 10);
  if (value <= 0) return null;

  const unit = (match[2] ?? "b").toLowerCase();
  const multiplier = UNIT_BYTES[unit];
  if (multiplier === undefined) return null;

  return value * multiplier;
}

/** Bytes of the configured minimum, for comparisons and error text. */
export const MIN_TLC_MEMORY_BYTES = parseMemoryBytes(MIN_TLC_MEMORY) ?? 512 * 1024 ** 2;

/**
 * The `-Xmx` argument for a container limited to `memoryBytes`.
 *
 * Whole megabytes, so the JVM accepts it verbatim: `"8g"` gives `-Xmx6144m`,
 * the pairing measured working on a model that had been dying silently.
 */
export function jvmHeapArg(memoryBytes: number): string {
  const megabytes = Math.max(64, Math.floor((memoryBytes * JVM_HEAP_FRACTION) / MEGABYTE));
  return `${megabytes}m`;
}

/**
 * `JAVA_TOOL_OPTIONS` for a TLC container.
 *
 * Passed as an environment variable rather than baked into the image's
 * entrypoint so a changed setting needs no image rebuild. `UseParallelGC` is
 * the collector TLC asks for by name in a warning it prints on every run
 * without it.
 */
export function javaToolOptions(memoryBytes: number): string {
  return `-Xmx${jvmHeapArg(memoryBytes)} -XX:+UseParallelGC`;
}
