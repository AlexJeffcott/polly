import { describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import { CONTAINER_NAME_PREFIX, mintContainerName } from "../../runner/container-name";
import { DockerRunner, removeContainer, sweepOrphanedContainers } from "../../runner/docker";

/**
 * polly#173 — a timed-out `docker run` must not leave its container behind.
 *
 * `--rm` is a *run*-time contract: the daemon removes the container when it
 * exits. Killing the local client is not killing the container, so before the
 * fix a timeout left an orphan the runner had no handle on. One orphan took the
 * SANY suite from 21.8s to 4148s.
 *
 * These tests start real containers. They are skipped when docker or the TLA+
 * image is absent, because the assertions are about daemon state.
 */

const IMAGE = "polly-tla:latest";

function dockerUsable(): boolean {
  // SKIP_DOCKER=1 is the repo's existing opt-out (see scripts/e2e-visualize.ts).
  if (process.env["SKIP_DOCKER"] === "1") return false;
  const info = spawnSync("docker", ["info"], { timeout: 10_000, stdio: "ignore" });
  if (info.status !== 0) return false;
  const image = spawnSync("docker", ["images", "-q", IMAGE], { timeout: 10_000, encoding: "utf8" });
  return (image.stdout ?? "").trim().length > 0;
}

function containerExists(name: string): boolean {
  const result = spawnSync(
    "docker",
    ["ps", "--all", "--filter", `name=^${name}$`, "--format", "{{.Names}}"],
    { timeout: 10_000, encoding: "utf8" }
  );
  return (result.stdout ?? "").trim() === name;
}

const usable = dockerUsable();

describe.skipIf(!usable)("container cleanup on timeout (polly#173)", () => {
  test("a timed-out docker run leaves no container behind", async () => {
    const docker = new DockerRunner();
    const containerName = mintContainerName("tlc");

    // A container that outlives the timeout by a wide margin. Before the fix
    // this survived the poll below; the client was killed and nothing else was.
    // --entrypoint overrides the image's `java -jar tla2tools.jar` wrapper; the
    // test is about container lifecycle, not about TLC.
    const args = ["run", "--rm", "--name", containerName, "--entrypoint", "sleep", IMAGE, "120"];

    await expect(
      docker.runCommand("docker", args, { timeout: 3000, containerName })
    ).rejects.toThrow(/timed out/);

    // The daemon removes asynchronously, so poll rather than assert immediately.
    const deadline = Date.now() + 20_000;
    while (containerExists(containerName) && Date.now() < deadline) {
      await new Promise((resolve) => setTimeout(resolve, 250));
    }

    const survived = containerExists(containerName);
    if (survived) removeContainer(containerName); // don't leak from a failing test
    expect(survived).toBe(false);
  }, 40_000);

  test("removeContainer is idempotent and never throws on an unknown name", () => {
    expect(() => removeContainer(`${CONTAINER_NAME_PREFIX}does-not-exist`)).not.toThrow();
  });

  test("the sweep only removes containers this runner named", () => {
    // A `Created` container outside the prefix must survive the sweep: the
    // machine this runs on has unrelated containers on it.
    const foreign = `not-polly-sweep-probe-${process.pid}`;
    spawnSync("docker", ["create", "--name", foreign, IMAGE, "sleep", "1"], {
      timeout: 30_000,
      stdio: "ignore",
    });

    try {
      const removed = sweepOrphanedContainers();
      expect(removed).not.toContain(foreign);
      expect(containerExists(foreign)).toBe(true);
    } finally {
      removeContainer(foreign);
    }
  }, 60_000);
});
