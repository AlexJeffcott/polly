// Architecture analysis - main orchestrator

import * as fs from "node:fs";
import * as path from "node:path";
import { type AnalysisProgram, type AnalysisSession, withAnalysisSession } from "../program";
import type {
  ArchitectureAnalysis,
  ContextInfo,
  ManifestInfo,
  ProjectConfig,
} from "../types/architecture";
import type { MessageHandler } from "../types/core";
import { extractADRs } from "./adr";
import { ContextAnalyzer } from "./contexts";
import { FlowAnalyzer } from "./flows";
import { HandlerExtractor } from "./handlers";
import { IntegrationAnalyzer } from "./integrations";
import { ManifestParser } from "./manifest";

export interface ArchitectureAnalysisOptions {
  /** Path to tsconfig.json */
  tsConfigPath: string;

  /** Project root directory */
  projectRoot: string;

  /** Optional: Override detected contexts */
  contexts?: string[];

  /** Optional: Use generic project detection (non-extension) */
  useProjectDetector?: boolean;

  /**
   * Optional: treat child directories holding a package.json as workspace
   * packages when the root package.json has no `workspaces` field.
   */
  inferWorkspaces?: boolean;

  /**
   * Optional: the typescript-7 session to run the handlers, contexts,
   * flows and integrations on (the caller closes it). Without one, `analyze` opens and
   * closes a session of its own.
   */
  session?: AnalysisSession;
}

export class ArchitectureAnalyzer {
  private options: ArchitectureAnalysisOptions;

  constructor(options: ArchitectureAnalysisOptions) {
    this.options = options;
  }

  /**
   * Perform complete architecture analysis
   */
  async analyze(): Promise<ArchitectureAnalysis> {
    const { session } = this.options;
    if (session) return this.analyzeWith(session);
    return withAnalysisSession((own) => this.analyzeWith(own));
  }

  private async analyzeWith(session: AnalysisSession): Promise<ArchitectureAnalysis> {
    // 1. Initialize system info and entry points
    const { manifest, projectConfig, entryPoints, systemInfo } = await this.initializeSystemInfo();

    // Build context overrides from monorepo workspace packages
    const contextOverrides = new Map<string, string>();
    if (projectConfig?.workspacePackages) {
      for (const pkg of projectConfig.workspacePackages) {
        // Map workspace path prefix to its context name
        contextOverrides.set(pkg.path, pkg.context);
      }
    }

    // Handlers, contexts, flows and integrations share one program (all AST
    // walks, plus go-to-definition for handlers and component prop types).
    const program = await session.open(this.options.tsConfigPath);

    // 2. Extract message handlers
    const handlerExtractor = new HandlerExtractor(
      this.options.tsConfigPath,
      contextOverrides.size > 0 ? contextOverrides : undefined
    );
    const { handlers, meshOrPeerSignals } = await handlerExtractor.extractHandlers(program);

    // 3. Analyze each context
    const contexts = await this.analyzeContexts(program, entryPoints, handlers);

    // 4. Analyze message flows
    const flowAnalyzer = new FlowAnalyzer(
      this.options.tsConfigPath,
      handlers,
      contextOverrides.size > 0 ? contextOverrides : undefined
    );
    const messageFlows = await flowAnalyzer.analyzeFlows(program);

    // 5. Analyze external integrations
    const integrationAnalyzer = new IntegrationAnalyzer(
      this.options.tsConfigPath,
      internalPackageNames(projectConfig)
    );
    const integrations = await integrationAnalyzer.analyzeIntegrations(program);

    // 6. Merge external API calls into context info
    this.mergeExternalAPIsIntoContexts(contexts, integrations);

    // 7. Extract ADRs (Architecture Decision Records)
    const adrs = extractADRs(this.options.projectRoot);

    // 8. Extract repository info
    const repository = this.extractRepositoryInfo();

    return {
      projectRoot: this.options.projectRoot,
      system: systemInfo,
      ...(manifest ? { manifest } : {}),
      ...(projectConfig ? { projectConfig } : {}),
      contexts,
      messageFlows,
      integrations,
      ...(meshOrPeerSignals.length > 0 ? { meshOrPeerSignals } : {}),
      ...(adrs.adrs.length > 0 ? { adrs } : {}),
      ...(repository ? { repository } : {}),
    };
  }

  /**
   * Initialize system information and entry points
   */
  private async initializeSystemInfo(): Promise<{
    manifest?: ManifestInfo;
    projectConfig?: ProjectConfig;
    entryPoints: Record<string, string>;
    systemInfo: { name: string; version: string; description?: string };
  }> {
    const manifestParser = new ManifestParser(this.options.projectRoot, true);

    if (manifestParser.hasManifest() && !this.options.useProjectDetector) {
      // Parse manifest.json (Chrome extension)
      const manifest = manifestParser.parse();
      const entryPoints = manifestParser.getContextEntryPoints();

      return {
        manifest,
        entryPoints,
        systemInfo: {
          name: manifest.name,
          version: manifest.version,
          ...(manifest.description ? { description: manifest.description } : {}),
        },
      };
    }

    // Use project detector for generic projects
    const { detectProjectConfig } = await import("./project-detector");
    const projectConfig = detectProjectConfig(this.options.projectRoot, {
      inferWorkspaces: this.options.inferWorkspaces === true,
    });

    return {
      projectConfig,
      entryPoints: projectConfig.entryPoints,
      systemInfo: {
        name: projectConfig.metadata?.name || "Unknown Project",
        version: projectConfig.metadata?.version || "0.0.0",
        ...(projectConfig.metadata?.description
          ? { description: projectConfig.metadata.description }
          : {}),
      },
    };
  }

  /**
   * Analyze all contexts from entry points
   */
  private async analyzeContexts(
    program: AnalysisProgram,
    entryPoints: Record<string, string>,
    handlers: MessageHandler[]
  ): Promise<Record<string, ContextInfo>> {
    const contextAnalyzer = new ContextAnalyzer(this.options.tsConfigPath);
    const contexts: Record<string, ContextInfo> = {};

    for (const [contextType, entryPoint] of Object.entries(entryPoints)) {
      try {
        const contextInfo = await contextAnalyzer.analyzeContext(
          contextType,
          entryPoint,
          handlers,
          program
        );
        contexts[contextType] = contextInfo;
      } catch (error) {
        // Skip contexts that fail to analyze
        if (process.env["POLLY_DEBUG"]) {
          console.log(`[DEBUG] Failed to analyze context ${contextType}: ${error}`);
        }
      }
    }

    return contexts;
  }

  /**
   * Merge external API calls into their respective contexts
   */
  private mergeExternalAPIsIntoContexts(
    contexts: Record<string, ContextInfo>,
    integrations: ExternalIntegration[]
  ): void {
    for (const integration of integrations) {
      if (integration.calls) {
        for (const call of integration.calls) {
          // Find which context this call belongs to
          for (const [contextType, contextInfo] of Object.entries(contexts)) {
            if (call.location.file.includes(`/${contextType}/`)) {
              contextInfo.externalAPIs.push(call);
              break;
            }
          }
        }
      }
    }
  }

  /**
   * Extract repository information from package.json
   */
  private extractRepositoryInfo(): ArchitectureAnalysis["repository"] {
    const packageJsonPath = path.join(this.options.projectRoot, "package.json");

    if (!fs.existsSync(packageJsonPath)) {
      return undefined;
    }

    try {
      const content = fs.readFileSync(packageJsonPath, "utf-8");
      const packageJson = JSON.parse(content);

      if (packageJson.repository) {
        if (typeof packageJson.repository === "string") {
          return {
            url: packageJson.repository,
            type: "git",
          };
        }

        return {
          url: packageJson.repository.url || packageJson.repository,
          type: packageJson.repository.type || "git",
        };
      }
    } catch (error) {
      // Skip if package.json is malformed or unreadable
      if (process.env["POLLY_DEBUG"]) {
        console.log(`[DEBUG] Failed to extract repository info from package.json: ${error}`);
      }
    }

    return undefined;
  }
}

/** The project's own package names: its workspace packages and itself. */
function internalPackageNames(projectConfig: ProjectConfig | undefined): string[] {
  const names = (projectConfig?.workspacePackages ?? []).map((pkg) => pkg.name);
  const own = projectConfig?.metadata?.name;
  return own ? [...names, own] : names;
}

/**
 * Convenience function to analyze architecture
 */
export async function analyzeArchitecture(
  options: ArchitectureAnalysisOptions
): Promise<ArchitectureAnalysis> {
  const analyzer = new ArchitectureAnalyzer(options);
  return analyzer.analyze();
}

// Fix: Import ExternalIntegration type
import type { ExternalIntegration } from "../types/architecture";
