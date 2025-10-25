// Architecture analysis - main orchestrator

import * as fs from "node:fs";
import * as path from "node:path";
import type { ArchitectureAnalysis, ContextInfo } from "../types/architecture";
import { ManifestParser } from "./manifest";
import { ContextAnalyzer } from "./contexts";
import { FlowAnalyzer } from "./flows";
import { IntegrationAnalyzer } from "./integrations";
import { HandlerExtractor } from "./handlers";
import { extractADRs } from "./adr";

export interface ArchitectureAnalysisOptions {
  /** Path to tsconfig.json */
  tsConfigPath: string;

  /** Project root directory (where manifest.json is) */
  projectRoot: string;

  /** Optional: Override detected contexts */
  contexts?: string[];
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
    // 1. Parse manifest.json
    const manifestParser = new ManifestParser(this.options.projectRoot);
    const manifest = manifestParser.parse();
    const entryPoints = manifestParser.getContextEntryPoints();

    // 2. Extract message handlers
    const handlerExtractor = new HandlerExtractor(this.options.tsConfigPath);
    const { handlers } = handlerExtractor.extractHandlers();

    // 3. Analyze each context
    const contextAnalyzer = new ContextAnalyzer(this.options.tsConfigPath);
    const contexts: Record<string, ContextInfo> = {};

    for (const [contextType, entryPoint] of Object.entries(entryPoints)) {
      try {
        const contextInfo = contextAnalyzer.analyzeContext(contextType, entryPoint, handlers);
        contexts[contextType] = contextInfo;
      } catch (error) {
        console.warn(`Failed to analyze context ${contextType}: ${error}`);
      }
    }

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
      system: {
        name: manifest.name,
        version: manifest.version,
        description: manifest.description,
      },
      manifest,
      contexts,
      messageFlows,
      integrations,
      adrs: adrs.adrs.length > 0 ? adrs : undefined,
      repository,
    };
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
      console.warn(`Failed to parse package.json: ${error}`);
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
