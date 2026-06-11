#!/usr/bin/env bun
// CLI for project initialization

import { existsSync } from "node:fs";
import {
  getAvailableTypes,
  getTemplateDir,
  type ProjectType,
  scaffoldFromTemplate,
  validateProjectName,
} from "./template-utils.ts";

function isAvailableType(value: string, available: ProjectType[]): value is ProjectType {
  const names: readonly string[] = available;
  return names.includes(value);
}

async function main() {
  const args = process.argv.slice(2);
  const cwd = process.cwd();

  // Parse arguments
  const projectName = args[0] || "my-project";
  const typeArg = args.find((arg) => arg.startsWith("--type="))?.split("=")[1] || "pwa";

  // Validate the requested type against the templates that actually ship,
  // before creating any directory. Asking for a type with no template used
  // to fail deep in the copy with a raw "Template directory not found" after
  // the project dir had already been made.
  const available = getAvailableTypes(import.meta.dir);
  if (!isAvailableType(typeArg, available)) {
    console.log(
      `\x1b[31m✗ Unknown or unavailable project type '${typeArg}'. Available: ${available.join(", ")}\x1b[0m\n`
    );
    process.exit(1);
  }
  const projectType = typeArg;

  // Validate project name
  const validation = validateProjectName(projectName);
  if (!validation.valid) {
    console.log(`\x1b[31m✗ ${validation.error}\x1b[0m\n`);
    process.exit(1);
  }

  const projectPath = `${cwd}/${projectName}`;

  // Check if directory already exists
  if (existsSync(projectPath)) {
    console.log(`\x1b[31m✗ Directory '${projectName}' already exists\x1b[0m\n`);
    process.exit(1);
  }

  // Get template directory
  const templateDir = getTemplateDir(projectType, import.meta.dir);

  // Scaffold project
  await scaffoldFromTemplate({
    projectName,
    projectPath,
    projectType,
    templateDir,
  });
}

main();
