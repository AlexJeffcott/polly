// Public API for @fairfox/polly/init
//
// Provides programmatic access to project initialization

export type {
  ProjectType,
  TemplateOptions,
} from "./template-utils.ts";

export {
  scaffoldFromTemplate,
  validateProjectName,
  getAvailableTypes,
  getTemplateDir,
  processTemplate,
} from "./template-utils.ts";

/**
 * Initialize a new Polly project
 *
 * @param projectName Name of the project to create
 * @param options Initialization options
 *
 * @example
 * ```typescript
 * import { initProject } from '@fairfox/polly/init'
 *
 * await initProject('my-app', {
 *   type: 'pwa',
 *   targetDir: './projects'
 * })
 * ```
 */
export async function initProject(
  projectName: string,
  options: {
    type?: "extension" | "pwa" | "websocket" | "generic";
    targetDir?: string;
  } = {}
): Promise<void> {
  const {
    scaffoldFromTemplate,
    validateProjectName,
    getTemplateDir,
  } = await import("./template-utils.ts");

  // Validate project name
  const validation = validateProjectName(projectName);
  if (!validation.valid) {
    throw new Error(validation.error);
  }

  const projectType = options.type || "pwa";
  const targetDir = options.targetDir || process.cwd();
  const projectPath = `${targetDir}/${projectName}`;

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
