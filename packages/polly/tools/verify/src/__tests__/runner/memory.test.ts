import { describe, expect, spyOn, test } from "bun:test";
import * as fs from "node:fs";
import { DockerRunner } from "../../runner/docker";
import {
  DEFAULT_TLC_MEMORY,
  javaToolOptions,
  jvmHeapArg,
  MIN_TLC_MEMORY_BYTES,
  parseMemoryBytes,
} from "../../runner/memory";

/**
 * polly#181: a TLC run with no memory ceiling.
 *
 * `docker run` got no `--memory` and the JVM got no `-Xmx`, so TLC sized its
 * heap from 25% of whatever Docker Desktop was allocated — 1984MB on one
 * machine, 6000MB on another, for the same spec on the same polly version. A
 * long run then died mid-check with no TLC message at all, killed by the host.
 */

/**
 * Drive `runTLC` with `docker` stubbed out and return the argv it built.
 */
async function captureDockerArgs(options?: {
  workers?: number;
  memory?: string;
}): Promise<string[]> {
  const docker = new DockerRunner();
  let capturedArgs: string[] = [];

  const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(
    async (_cmd: string, args: string[]) => {
      capturedArgs = args;
      return { exitCode: 0, stdout: "", stderr: "" };
    }
  );
  const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
  const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
    /* no-op mock */
  });

  try {
    await docker.runTLC("/path/to/spec.tla", { workers: 1, ...options });
    return capturedArgs;
  } finally {
    runCommandSpy.mockRestore();
    existsSyncSpy.mockRestore();
    rmSyncSpy.mockRestore();
  }
}

/** Drive `runTLC` against a stubbed docker result and return what it parsed. */
async function runWithDockerResult(result: { exitCode: number; stdout: string; stderr: string }) {
  const docker = new DockerRunner();
  const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(async () => result);
  const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
  const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
    /* no-op mock */
  });

  try {
    return await docker.runTLC("/path/to/spec.tla", { workers: 1, memory: "8g" });
  } finally {
    runCommandSpy.mockRestore();
    existsSyncSpy.mockRestore();
    rmSyncSpy.mockRestore();
  }
}

/** The value of a `docker run` flag, e.g. `--memory` or `-e`. */
function flagValue(args: string[], flag: string): string | undefined {
  const index = args.indexOf(flag);
  return index === -1 ? undefined : args[index + 1];
}

describe("parseMemoryBytes", () => {
  test("reads docker-style suffixes", () => {
    expect(parseMemoryBytes("512m")).toBe(512 * 1024 ** 2);
    expect(parseMemoryBytes("8g")).toBe(8 * 1024 ** 3);
    expect(parseMemoryBytes("1024k")).toBe(1024 * 1024);
    expect(parseMemoryBytes("2048b")).toBe(2048);
  });

  test("a bare number is bytes, as docker reads it", () => {
    expect(parseMemoryBytes("1073741824")).toBe(1024 ** 3);
  });

  test("case and surrounding space do not matter", () => {
    expect(parseMemoryBytes(" 8G ")).toBe(8 * 1024 ** 3);
  });

  test("rejects what docker would reject, rather than guessing", () => {
    expect(parseMemoryBytes("8gb")).toBeNull();
    expect(parseMemoryBytes("lots")).toBeNull();
    expect(parseMemoryBytes("")).toBeNull();
    expect(parseMemoryBytes("0g")).toBeNull();
    expect(parseMemoryBytes("-4g")).toBeNull();
    expect(parseMemoryBytes("1.5g")).toBeNull();
  });
});

describe("jvmHeapArg", () => {
  test('"8g" gives the -Xmx6g measured working on a model that had been dying', () => {
    expect(jvmHeapArg(8 * 1024 ** 3)).toBe("6144m");
  });

  test("the heap always sits under the container limit", () => {
    for (const spec of ["512m", "1g", "4g", "8g", "16g"]) {
      const bytes = parseMemoryBytes(spec);
      if (bytes === null) throw new Error(`${spec} did not parse`);
      const heapMegabytes = Number.parseInt(jvmHeapArg(bytes), 10);
      // Non-heap use — TLC's off-heap fingerprint set, metaspace, thread
      // stacks — sits outside -Xmx and inside --memory.
      expect(heapMegabytes * 1024 ** 2).toBeLessThan(bytes);
    }
  });

  test("asks for the collector TLC warns about on every run without it", () => {
    expect(javaToolOptions(4 * 1024 ** 3)).toContain("-XX:+UseParallelGC");
    expect(javaToolOptions(4 * 1024 ** 3)).toContain("-Xmx3072m");
  });
});

describe("DockerRunner.runTLC memory ceiling", () => {
  test("passes --memory to docker run", async () => {
    const args = await captureDockerArgs({ memory: "8g" });

    expect(flagValue(args, "--memory")).toBe("8g");
  });

  test("caps the JVM heap under the container limit, in the same run", async () => {
    const args = await captureDockerArgs({ memory: "8g" });

    expect(flagValue(args, "-e")).toBe("JAVA_TOOL_OPTIONS=-Xmx6144m -XX:+UseParallelGC");
  });

  test("an unset memory uses the fixed default, never unbounded", async () => {
    const args = await captureDockerArgs();

    expect(args).toContain("--memory");
    expect(flagValue(args, "--memory")).toBe(DEFAULT_TLC_MEMORY);
  });

  test("the default is a fixed value, not a fraction of this host", () => {
    // Reproducibility across machines is the whole point: two Docker Desktop
    // allocations must give TLC the same heap.
    expect(parseMemoryBytes(DEFAULT_TLC_MEMORY)).toBeGreaterThanOrEqual(MIN_TLC_MEMORY_BYTES);
  });

  test("both flags precede the image name, or docker reads them as TLC arguments", async () => {
    const args = await captureDockerArgs({ memory: "8g" });

    const imageIndex = args.indexOf("polly-tla:latest");
    expect(imageIndex).toBeGreaterThan(-1);
    expect(args.indexOf("--memory")).toBeLessThan(imageIndex);
    expect(args.indexOf("-e")).toBeLessThan(imageIndex);
  });

  test("a memory string docker would reject fails before the run starts", async () => {
    expect(captureDockerArgs({ memory: "8gb" })).rejects.toThrow(/Invalid verification.memory/);
  });
});

describe("running out of the ceiling", () => {
  test("the JVM's own OutOfMemoryError is surfaced, with the ceiling that was set", async () => {
    const result = await runWithDockerResult({
      exitCode: 1,
      stdout: "Computing initial states...\n",
      stderr: 'Exception in thread "main" java.lang.OutOfMemoryError: Java heap space\n',
    });

    expect(result.success).toBe(false);
    expect(result.error).toContain("out of heap");
    expect(result.error).toContain("8g");
  });

  test("a cgroup kill (137) is named as a memory kill, not an unknown error", async () => {
    const result = await runWithDockerResult({
      exitCode: 137,
      stdout: "Progress(4) at 2026-09-08 13:03:11: 4818421 states generated\n",
      stderr: "",
    });

    expect(result.success).toBe(false);
    expect(result.error).toContain("container memory limit");
    expect(result.error).toContain("8g");
  });

  test("a killed run reports no state count at all", async () => {
    const result = await runWithDockerResult({ exitCode: 137, stdout: "", stderr: "" });

    expect(result.stats).toBeUndefined();
  });
});
