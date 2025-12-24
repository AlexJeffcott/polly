// Docker container management for TLA+ verification

import { spawn } from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

export type DockerRunResult = {
  exitCode: number;
  stdout: string;
  stderr: string;
};

export class DockerRunner {
  /**
   * Check if Docker is available
   */
  async isDockerAvailable(): Promise<boolean> {
    try {
      const result = await this.runCommand("docker", ["--version"]);
      return result.exitCode === 0;
    } catch {
      return false;
    }
  }

  /**
   * Check if TLA+ image exists
   */
  async hasImage(): Promise<boolean> {
    try {
      const result = await this.runCommand("docker", ["images", "-q", "talex5/tla"]);
      return result.stdout.trim().length > 0;
    } catch {
      return false;
    }
  }

  /**
   * Pull TLA+ image
   */
  async pullImage(onProgress?: (line: string) => void): Promise<void> {
    await this.runCommandStreaming("docker", ["pull", "talex5/tla:latest"], onProgress);
  }

  /**
   * Run TLC model checker on a spec
   */
  async runTLC(
    specPath: string,
    options?: {
      workers?: number;
      timeout?: number;
    }
  ): Promise<TLCResult> {
    // Ensure spec file exists
    if (!fs.existsSync(specPath)) {
      throw new Error(`Spec file not found: ${specPath}`);
    }

    const specDir = path.dirname(specPath);
    const specName = path.basename(specPath, ".tla");
    const cfgPath = path.join(specDir, `${specName}.cfg`);

    // Ensure cfg file exists
    if (!fs.existsSync(cfgPath)) {
      throw new Error(`Config file not found: ${cfgPath}`);
    }

    // Run TLC in Docker
    // Use sh -c to cd into /specs directory so TLC can find imported modules
    const args = [
      "run",
      "--rm",
      "-v",
      `${specDir}:/specs`,
      "talex5/tla",
      "sh",
      "-c",
      `cd /specs && tlc -workers ${options?.workers || 1} ${specName}.tla`,
    ];

    const result = await this.runCommand("docker", args, {
      timeout: options?.timeout || 60000,
    });

    return this.parseTLCOutput(result);
  }

  /**
   * Parse TLC output
   */
  private parseTLCOutput(result: DockerRunResult): TLCResult {
    const output = result.stdout + result.stderr;

    // Check for violations
    const violationMatch = output.match(/Error: Invariant (.*?) is violated/);
    if (violationMatch) {
      return {
        success: false,
        violation: {
          type: "invariant",
          name: violationMatch[1],
          trace: this.extractTrace(output),
        },
        output,
      };
    }

    // Check for errors
    if (result.exitCode !== 0 || output.includes("Error:")) {
      return {
        success: false,
        error: this.extractError(output),
        output,
      };
    }

    // Success
    const statesMatch = output.match(/(\d+) states generated/);
    const distinctMatch = output.match(/(\d+) distinct states/);

    return {
      success: true,
      stats: {
        statesGenerated: statesMatch?.[1] ? Number.parseInt(statesMatch[1]) : 0,
        distinctStates: distinctMatch?.[1] ? Number.parseInt(distinctMatch[1]) : 0,
      },
      output,
    };
  }

  /**
   * Extract error trace from TLC output
   */
  private extractTrace(output: string): string[] {
    const lines = output.split("\n");
    const trace: string[] = [];
    let inTrace = false;

    for (const line of lines) {
      if (line.includes("State ") && line.includes(":")) {
        inTrace = true;
        trace.push(line);
      } else if (inTrace) {
        if (line.trim() === "" || line.startsWith("Error:")) {
          break;
        }
        trace.push(line);
      }
    }

    return trace;
  }

  /**
   * Extract error message from TLC output
   */
  private extractError(output: string): string {
    const errorMatch = output.match(/Error: (.*?)(?:\n|$)/);
    if (errorMatch?.[1]) {
      return errorMatch[1];
    }

    // Look for common error patterns
    if (output.includes("Parse Error")) {
      return "TLA+ syntax error in specification";
    }
    if (output.includes("Semantic Error")) {
      return "Semantic error in specification";
    }

    return "Unknown error occurred during model checking";
  }

  /**
   * Run a command and return output
   * Public to allow other runners (like SANYRunner) to execute commands
   */
  runCommand(
    command: string,
    args: string[],
    options?: { timeout?: number }
  ): Promise<DockerRunResult> {
    return new Promise((resolve, reject) => {
      const proc = spawn(command, args);

      let stdout = "";
      let stderr = "";

      proc.stdout.on("data", (data) => {
        stdout += data.toString();
      });

      proc.stderr.on("data", (data) => {
        stderr += data.toString();
      });

      const timeout = options?.timeout
        ? setTimeout(() => {
            proc.kill();
            reject(new Error(`Command timed out after ${options.timeout}ms`));
          }, options.timeout)
        : null;

      proc.on("close", (exitCode) => {
        if (timeout) clearTimeout(timeout);

        resolve({
          exitCode: exitCode || 0,
          stdout,
          stderr,
        });
      });

      proc.on("error", (error) => {
        if (timeout) clearTimeout(timeout);
        reject(error);
      });
    });
  }

  /**
   * Run a command with streaming output
   */
  private runCommandStreaming(
    command: string,
    args: string[],
    onOutput?: (line: string) => void
  ): Promise<void> {
    return new Promise((resolve, reject) => {
      const proc = spawn(command, args);

      proc.stdout.on("data", (data) => {
        if (onOutput) {
          const lines = data.toString().split("\n");
          for (const line of lines) {
            if (line.trim()) {
              onOutput(line.trim());
            }
          }
        }
      });

      proc.stderr.on("data", (data) => {
        if (onOutput) {
          const lines = data.toString().split("\n");
          for (const line of lines) {
            if (line.trim()) {
              onOutput(line.trim());
            }
          }
        }
      });

      proc.on("close", (exitCode) => {
        if (exitCode === 0) {
          resolve();
        } else {
          reject(new Error(`Command failed with exit code ${exitCode}`));
        }
      });

      proc.on("error", reject);
    });
  }
}

export type TLCResult = {
  success: boolean;
  violation?: {
    type: "invariant" | "property" | "deadlock";
    name?: string;
    trace: string[];
  };
  error?: string;
  stats?: {
    statesGenerated: number;
    distinctStates: number;
  };
  output: string;
};
