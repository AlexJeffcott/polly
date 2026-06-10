/**
 * Template utilities for project initialization
 */

import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

export type ProjectType = "extension" | "pwa" | "websocket" | "generic";

export interface TemplateOptions {
  projectName: string;
  projectPath: string;
  projectType: ProjectType;
  templateDir: string;
}

/**
 * Process template file and replace placeholders
 */
export function processTemplate(content: string, projectName: string): string {
  return content
    .replace(/\{\{PROJECT_NAME\}\}/g, projectName)
    .replace(/\{\{PROJECT_NAME_UPPER\}\}/g, projectName.toUpperCase())
    .replace(/\{\{PROJECT_NAME_CAMEL\}\}/g, toCamelCase(projectName));
}

/**
 * Convert string to camelCase
 */
function toCamelCase(str: string): string {
  return str
    .replace(/[-_](.)/g, (_, char) => char.toUpperCase())
    .replace(/^(.)/, (char) => char.toLowerCase());
}

/**
 * Copy template directory to project
 */
export async function scaffoldFromTemplate(options: TemplateOptions): Promise<void> {
  const { projectName, projectPath, templateDir } = options;

  // Create project directory
  mkdirSync(projectPath, { recursive: true });

  // Copy all template files
  copyTemplateFiles(templateDir, projectPath, projectName);
}

/**
 * Recursively copy template files and process them
 */
function copyTemplateFiles(
  sourceDir: string,
  targetDir: string,
  projectName: string,
  relativePath = ""
): void {
  if (!existsSync(sourceDir)) {
    throw new Error(`Template directory not found: ${sourceDir}`);
  }

  const entries = readdirSync(sourceDir, { withFileTypes: true });

  for (const entry of entries) {
    const sourcePath = join(sourceDir, entry.name);
    const targetPath = join(targetDir, relativePath, entry.name.replace(".template", ""));

    if (entry.isDirectory()) {
      // Create directory and recurse
      mkdirSync(targetPath, { recursive: true });
      copyTemplateFiles(sourcePath, targetDir, projectName, join(relativePath, entry.name));
    } else if (entry.name.endsWith(".template")) {
      // Process template file
      const content = readFileSync(sourcePath, "utf-8");
      const processed = processTemplate(content, projectName);
      writeFileSync(targetPath, processed, "utf-8");
    } else {
      // Copy binary files as-is
      cpSync(sourcePath, targetPath);
    }
  }
}

/** Every project type the scaffolder knows how to name. A type is only
 *  *available* once a matching template directory ships next to this
 *  module — see {@link getAvailableTypes}. */
const ALL_PROJECT_TYPES: ProjectType[] = ["extension", "pwa", "websocket", "generic"];

/**
 * Get the project types that can actually be scaffolded — the subset of
 * {@link ALL_PROJECT_TYPES} that has a template directory on disk. Derived
 * from the filesystem so the list cannot drift from reality: advertising a
 * type whose template was never written is exactly the gap that left
 * `polly init` (default `extension`) pointing at a missing directory.
 */
export function getAvailableTypes(baseDir: string = import.meta.dir): ProjectType[] {
  const templatesRoot = join(baseDir, "..", "templates");
  let present: string[];
  try {
    present = readdirSync(templatesRoot, { withFileTypes: true })
      .filter((entry) => entry.isDirectory())
      .map((entry) => entry.name);
  } catch {
    return [];
  }
  return ALL_PROJECT_TYPES.filter((type) => present.includes(type));
}

/**
 * Get template directory for project type
 */
export function getTemplateDir(projectType: ProjectType, baseDir: string): string {
  return join(baseDir, "..", "templates", projectType);
}

/**
 * Validate project name
 */
export function validateProjectName(name: string): {
  valid: boolean;
  error?: string;
} {
  if (!name || name.trim().length === 0) {
    return { valid: false, error: "Project name cannot be empty" };
  }

  if (!/^[a-z0-9-_]+$/i.test(name)) {
    return {
      valid: false,
      error: "Project name can only contain letters, numbers, hyphens, and underscores",
    };
  }

  if (name.startsWith("-") || name.startsWith("_")) {
    return {
      valid: false,
      error: "Project name cannot start with a hyphen or underscore",
    };
  }

  return { valid: true };
}
