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
  });
});
