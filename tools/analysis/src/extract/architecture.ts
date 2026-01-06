// Architecture analysis - main orchestrator

import * as fs from "node:fs";
import * as path from "node:path";
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
}

/**
 * Comprehensive architecture analyzer
 */
export class ArchitectureAnalyzer {
  private options: ArchitectureAnalysisOptions;

  constructor(options: ArchitectureAnalysisOptions) {
    this.options = options;
  }

  /**
   * Perform complete architecture analysis
   */
  async analyze(): Promise<ArchitectureAnalysis> {
    // 1. Initialize system info and entry points
    const { manifest, projectConfig, entryPoints, systemInfo } = await this.initializeSystemInfo();

    // 2. Extract message handlers
    const handlerExtractor = new HandlerExtractor(this.options.tsConfigPath);
    const { handlers } = handlerExtractor.extractHandlers();

    // 3. Analyze each context
    const contexts = this.analyzeContexts(entryPoints, handlers);

    // 4. Analyze message flows
    const flowAnalyzer = new FlowAnalyzer(this.options.tsConfigPath, handlers);
    const messageFlows = flowAnalyzer.analyzeFlows();

    // 5. Analyze external integrations
    const integrationAnalyzer = new IntegrationAnalyzer(this.options.tsConfigPath);
    const integrations = integrationAnalyzer.analyzeIntegrations();

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
    const projectConfig = detectProjectConfig(this.options.projectRoot);

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
  private analyzeContexts(
    entryPoints: Record<string, string>,
    handlers: MessageHandler[]
  ): Record<string, ContextInfo> {
    const contextAnalyzer = new ContextAnalyzer(this.options.tsConfigPath);
    const contexts: Record<string, ContextInfo> = {};

    for (const [contextType, entryPoint] of Object.entries(entryPoints)) {
      try {
        const contextInfo = contextAnalyzer.analyzeContext(contextType, entryPoint, handlers);
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
