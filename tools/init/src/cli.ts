#!/usr/bin/env bun
// CLI for project initialization

import { existsSync } from "node:fs";
import {
  getTemplateDir,
  type ProjectType,
  scaffoldFromTemplate,
  validateProjectName,
} from "./template-utils.ts";

async function main() {
  const args = process.argv.slice(2);
  const cwd = process.cwd();

  // Parse arguments
  const projectName = args[0] || "my-project";
  const typeArg = args.find((arg) => arg.startsWith("--type="))?.split("=")[1] || "extension";
  const projectType = typeArg as ProjectType;

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
