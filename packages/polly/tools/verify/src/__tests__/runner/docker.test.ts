import { describe, expect, spyOn, test } from "bun:test";
import * as fs from "node:fs";
import { DockerRunner } from "../../runner/docker";

describe("DockerRunner", () => {
  describe("runTLC", () => {
    test("includes -depth flag when maxDepth is specified", async () => {
      const docker = new DockerRunner();

      // Track the args passed to runCommand
      let capturedArgs: string[] = [];

      // Spy on runCommand to capture the docker args
      const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(
        async (_cmd: string, args: string[]) => {
          capturedArgs = args;
          return { exitCode: 0, stdout: "0 states generated", stderr: "" };
        }
      );

      // Mock fs.existsSync to return true for spec and cfg files
      const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
      const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
        /* no-op mock */
      });

      try {
        await docker.runTLC("/path/to/spec.tla", {
          workers: 2,
          maxDepth: 7,
        });

        // Verify -depth flag is included
        expect(capturedArgs).toContain("-depth");
        expect(capturedArgs).toContain("7");

        // Verify the order: -depth should come before the spec file
        const depthIndex = capturedArgs.indexOf("-depth");
        const specIndex = capturedArgs.indexOf("spec.tla");
        expect(depthIndex).toBeLessThan(specIndex);
        expect(capturedArgs[depthIndex + 1]).toBe("7");
      } finally {
        runCommandSpy.mockRestore();
        existsSyncSpy.mockRestore();
        rmSyncSpy.mockRestore();
      }
    });

    test("does not include -depth flag when maxDepth is not specified", async () => {
      const docker = new DockerRunner();

      let capturedArgs: string[] = [];

      const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(
        async (_cmd: string, args: string[]) => {
          capturedArgs = args;
          return { exitCode: 0, stdout: "0 states generated", stderr: "" };
        }
      );

      const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
      const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
        /* no-op mock */
      });

      try {
        await docker.runTLC("/path/to/spec.tla", {
          workers: 2,
        });

        // Verify -depth flag is NOT included
        expect(capturedArgs).not.toContain("-depth");
      } finally {
        runCommandSpy.mockRestore();
        existsSyncSpy.mockRestore();
        rmSyncSpy.mockRestore();
      }
    });

    test("does not include -depth flag when maxDepth is 0", async () => {
      const docker = new DockerRunner();

      let capturedArgs: string[] = [];

      const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(
        async (_cmd: string, args: string[]) => {
          capturedArgs = args;
          return { exitCode: 0, stdout: "0 states generated", stderr: "" };
        }
      );

      const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
      const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
        /* no-op mock */
      });

      try {
        await docker.runTLC("/path/to/spec.tla", {
          workers: 2,
          maxDepth: 0,
        });

        // Verify -depth flag is NOT included when maxDepth is 0
        expect(capturedArgs).not.toContain("-depth");
      } finally {
        runCommandSpy.mockRestore();
        existsSyncSpy.mockRestore();
        rmSyncSpy.mockRestore();
      }
    });

    test("includes -workers and -cleanup flags", async () => {
      const docker = new DockerRunner();

      let capturedArgs: string[] = [];

      const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(
        async (_cmd: string, args: string[]) => {
          capturedArgs = args;
          return { exitCode: 0, stdout: "0 states generated", stderr: "" };
        }
      );

      const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
      const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
        /* no-op mock */
      });

      try {
        await docker.runTLC("/path/to/spec.tla", {
          workers: 4,
        });

        // Verify standard flags are included
        expect(capturedArgs).toContain("-workers");
        expect(capturedArgs).toContain("4");
        expect(capturedArgs).toContain("-cleanup");
        expect(capturedArgs).toContain("tlc");
      } finally {
        runCommandSpy.mockRestore();
        existsSyncSpy.mockRestore();
        rmSyncSpy.mockRestore();
      }
    });

    test("writes the state pool to a container-internal -metadir (#152)", async () => {
      const docker = new DockerRunner();

      let capturedArgs: string[] = [];

      const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(
        async (_cmd: string, args: string[]) => {
          capturedArgs = args;
          return { exitCode: 0, stdout: "0 states generated", stderr: "" };
        }
      );

      const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
      const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
        /* no-op mock */
      });

      try {
        await docker.runTLC("/path/to/spec.tla", { workers: 1 });

        // The state pool must be pointed off the host bind mount so it doesn't
        // traverse Docker Desktop's file-share layer during large runs.
        expect(capturedArgs).toContain("-metadir");
        const metadirIndex = capturedArgs.indexOf("-metadir");
        expect(capturedArgs[metadirIndex + 1]).toBe("/tmp/states");

        // It must point at a container-internal path, never back into /work
        // (the bind mount).
        expect(capturedArgs[metadirIndex + 1]).not.toContain("/work");

        // -metadir must come before the spec file, like the other TLC flags.
        const specIndex = capturedArgs.indexOf("spec.tla");
        expect(metadirIndex).toBeLessThan(specIndex);
      } finally {
        runCommandSpy.mockRestore();
        existsSyncSpy.mockRestore();
        rmSyncSpy.mockRestore();
      }
    });
  });

  describe("parseTLCOutput", () => {
    test("reports a state-pool IO flake distinctly from a spec error (#152)", async () => {
      const docker = new DockerRunner();

      const ioFailureOutput = [
        "Error: when writing the disk (StatePoolWriter.run):",
        "states/26-05-28-19-38-39/22403 (No such file or directory)",
      ].join("\n");

      const runCommandSpy = spyOn(docker, "runCommand").mockImplementation(async () => ({
        exitCode: 1,
        stdout: ioFailureOutput,
        stderr: "",
      }));

      const existsSyncSpy = spyOn(fs, "existsSync").mockReturnValue(true);
      const rmSyncSpy = spyOn(fs, "rmSync").mockImplementation(() => {
        /* no-op mock */
      });

      try {
        const result = await docker.runTLC("/path/to/spec.tla", { workers: 1 });

        expect(result.success).toBe(false);
        expect(result.error).toContain("state-pool IO failure");
        expect(result.error).toContain("re-run");
        // It must NOT be reported as a generic/spec error.
        expect(result.error).not.toBe("Unknown error occurred during model checking");
      } finally {
        runCommandSpy.mockRestore();
        existsSyncSpy.mockRestore();
        rmSyncSpy.mockRestore();
      }
    });
  });
});
