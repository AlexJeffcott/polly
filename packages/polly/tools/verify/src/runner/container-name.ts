/**
 * Unique, greppable names for the containers this runner starts (polly#173).
 *
 * `docker run --rm` is a *run*-time contract: the daemon removes the container
 * when it exits. A container that stalls during creation never starts, so it
 * never exits, so `--rm` never fires — and killing the local `docker` client
 * (the runner's only other lever) does not touch the container on the daemon.
 * Without a name there is no handle left to remove it by, because the client
 * that knew the id is gone. Each orphan degrades subsequent container creation,
 * so one stall produces more stalls and more orphans.
 *
 * Naming every run fixes that: the timeout arm removes by name, and a startup
 * sweep recovers from a hard kill where no timeout handler runs at all.
 *
 * `Date.now()` alone is NOT sufficient — it is millisecond-granular, and two
 * names minted in the same millisecond collide, at which point the timeout path
 * removes the *wrong* container. The pid plus a monotonic counter makes the
 * name unique within a process, and randomness makes it unique across them.
 */

/** Every name this module mints starts here, so a sweep can match them. */
export const CONTAINER_NAME_PREFIX = "polly-tla-";

let counter = 0;

/**
 * Mint a container name unique across processes and within one.
 *
 * @param kind Short tag naming the workload (e.g. `"tlc"`, `"sany"`), so a
 *             `docker ps` during a run says which stage is hanging.
 */
export function mintContainerName(kind: string): string {
  counter += 1;
  const unique = crypto.randomUUID().slice(0, 8);
  return `${CONTAINER_NAME_PREFIX}${sanitizeKind(kind)}-${process.pid}-${counter}-${unique}`;
}

/**
 * Docker names must match `[a-zA-Z0-9][a-zA-Z0-9_.-]*`. The prefix supplies a
 * valid first character, so the tag only has to avoid illegal characters.
 */
function sanitizeKind(kind: string): string {
  const cleaned = kind.replace(/[^a-zA-Z0-9_.-]/g, "-");
  return cleaned.length > 0 ? cleaned : "run";
}
