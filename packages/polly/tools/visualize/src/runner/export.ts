// Export static site using Structurizr CLI
// Uses Docker to run Structurizr CLI for generating a static HTML site

import { spawn } from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

export interface ExportOptions {
  /** DSL file path */
  dslPath: string;

  /** Output directory for static site */
  outputDir: string;

  /** Timeout in milliseconds */
  timeout?: number;

  /** Callback for progress updates */
  onProgress?: (message: string) => void;
}

export interface ExportResult {
  success: boolean;
  siteDir: string;
  error?: string;
}

export class DiagramExporter {
  private static readonly DOCKER_IMAGE = "structurizr/cli:latest";
  private static readonly DEFAULT_TIMEOUT = 120000; // 2 minutes

  /**
   * Export static site using Structurizr CLI via Docker
   */
  async export(options: ExportOptions): Promise<ExportResult> {
    const { dslPath, outputDir, timeout = DiagramExporter.DEFAULT_TIMEOUT } = options;

    // Validate DSL file exists
    if (!fs.existsSync(dslPath)) {
      return {
        success: false,
        siteDir: "",
        error: `DSL file not found: ${dslPath}`,
      };
    }

    // Ensure output directory exists
    if (!fs.existsSync(outputDir)) {
      fs.mkdirSync(outputDir, { recursive: true });
    }

    // Check if Docker is available
    const dockerAvailable = await this.isDockerAvailable();
    if (!dockerAvailable) {
      return {
        success: false,
        siteDir: "",
        error: "Docker is not available. Please install Docker to export the site.",
      };
    }

    // Pull image if needed
    options.onProgress?.("Checking Structurizr CLI image...");
    const hasImage = await this.hasImage();
    if (!hasImage) {
      options.onProgress?.("Pulling Structurizr CLI image (this may take a moment)...");
      await this.pullImage((line) => options.onProgress?.(line));
    }

    // Export static site
    options.onProgress?.("Generating static site...");

    try {
      await this.exportStaticSite(dslPath, outputDir, timeout);
      options.onProgress?.("✓ Static site generated successfully");

      return {
        success: true,
        siteDir: outputDir,
      };
    } catch (error) {
      return {
        success: false,
        siteDir: "",
        error: `Failed to export static site: ${error}`,
      };
    }
  }

  /**
   * Export static HTML site using Structurizr CLI
   */
  private async exportStaticSite(
    dslPath: string,
    outputDir: string,
    timeout: number
  ): Promise<void> {
    const dslDir = path.dirname(dslPath);
    const dslFileName = path.basename(dslPath);

    // Docker volume mounts
    const workspaceMount = `${dslDir}:/usr/local/structurizr`;
    const outputMount = `${outputDir}:/output`;

    // Structurizr CLI command for static site export
    const args = [
      "run",
      "--rm",
      "-v",
      workspaceMount,
      "-v",
      outputMount,
      DiagramExporter.DOCKER_IMAGE,
      "export",
      "-workspace",
      `/usr/local/structurizr/${dslFileName}`,
      "-format",
      "static",
      "-output",
      "/output",
    ];

    await this.runDocker(args, timeout);
  }

  /**
   * Check if Docker is available
   */
  async isDockerAvailable(): Promise<boolean> {
    try {
      await this.runCommand("docker", ["--version"], 5000);
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Check if Structurizr CLI image is available
   */
  async hasImage(): Promise<boolean> {
    try {
      const output = await this.runCommand(
        "docker",
        ["images", "-q", DiagramExporter.DOCKER_IMAGE],
        5000
      );
      return output.trim().length > 0;
    } catch {
      return false;
    }
  }

  /**
   * Pull Structurizr CLI image
   */
  async pullImage(onProgress?: (line: string) => void): Promise<void> {
    return new Promise((resolve, reject) => {
      const proc = spawn("docker", ["pull", DiagramExporter.DOCKER_IMAGE]);

      proc.stdout.on("data", (data) => {
        onProgress?.(data.toString().trim());
      });

      proc.stderr.on("data", (data) => {
        onProgress?.(data.toString().trim());
      });

      proc.on("close", (code) => {
        if (code === 0) {
          resolve();
        } else {
          reject(new Error(`Failed to pull image, exit code: ${code}`));
        }
      });

      proc.on("error", (error) => {
        reject(error);
      });
    });
  }

  /**
   * Run Docker command
   */
  private async runDocker(args: string[], timeout: number): Promise<string> {
    return this.runCommand("docker", args, timeout);
  }

  /**
   * Run shell command
   */
  private async runCommand(command: string, args: string[], timeout: number): Promise<string> {
    return new Promise((resolve, reject) => {
      const proc = spawn(command, args);
      let stdout = "";
      let stderr = "";

      const timer = setTimeout(() => {
        proc.kill();
        reject(new Error(`Command timed out after ${timeout}ms`));
      }, timeout);

      proc.stdout.on("data", (data) => {
        stdout += data.toString();
      });

      proc.stderr.on("data", (data) => {
        stderr += data.toString();
      });

      proc.on("close", (code) => {
        clearTimeout(timer);
        if (code === 0) {
          resolve(stdout);
        } else {
          reject(new Error(`Command failed with exit code ${code}: ${stderr}`));
        }
      });

      proc.on("error", (error) => {
        clearTimeout(timer);
        reject(error);
      });
    });
  }
}

/**
 * Export diagrams
 */
export async function exportDiagrams(options: ExportOptions): Promise<ExportResult> {
  const exporter = new DiagramExporter();
  return exporter.export(options);
}
