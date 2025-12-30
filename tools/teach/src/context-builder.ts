// Context builder for Claude-powered teaching session

import * as fs from "node:fs";
import * as path from "node:path";
import type {
  ArchitectureAnalysis,
  ContextInfo,
  MessageFlow,
} from "../../analysis/src/types/architecture.ts";

export interface TeachingContext {
  project: {
    root: string;
    architecture: ArchitectureAnalysis;
    summary: string;
  };
  verification?: {
    config?: unknown;
    lastResults?: {
      success: boolean;
      stats?: { statesGenerated: number; distinctStates: number };
      violation?: { name: string; trace: string[] };
      error?: string;
      timestamp?: Date;
    };
  };
  codebase: {
    tsConfigPath: string;
    stateFilePath?: string;
  };
}

/**
 * Build comprehensive teaching context from project analysis
 */
export async function buildTeachingContext(
  projectRoot: string,
  analysis: ArchitectureAnalysis
): Promise<TeachingContext> {
  const contexts = Object.entries(analysis.contexts) as [string, ContextInfo][];
  const allHandlers = contexts.flatMap(([_, ctx]) => ctx.handlers || []);
  const messageFlows = analysis.messageFlows || [];

  const summary = generateArchitectureSummary(contexts, allHandlers, messageFlows);

  const context: TeachingContext = {
    project: {
      root: projectRoot,
      architecture: analysis,
      summary,
    },
    codebase: {
      tsConfigPath: findTsConfig(projectRoot) || `${projectRoot}/tsconfig.json`,
      stateFilePath: findStateFile(projectRoot),
    },
  };

  // Try to load verification config and results
  const verification = await loadVerificationInfo(projectRoot);
  if (verification) {
    context.verification = verification;
  }

  return context;
}

function generateArchitectureSummary(
  contexts: [string, ContextInfo][],
  handlers: unknown[],
  flows: MessageFlow[]
): string {
  const parts = [
    `Project contains ${contexts.length} context(s) and ${handlers.length} message handler(s).`,
  ];

  if (flows.length > 0) {
    parts.push(`${flows.length} message flow(s) detected between contexts.`);
  }

  const stateVariablesCount = contexts.reduce((sum, [_, ctx]) => {
    return sum + Object.keys(ctx.state?.variables || {}).length;
  }, 0);

  if (stateVariablesCount > 0) {
    parts.push(`${stateVariablesCount} total state variables tracked across contexts.`);
  }

  return parts.join(" ");
}

async function loadVerificationInfo(
  projectRoot: string
): Promise<TeachingContext["verification"] | null> {
  const configPath = path.join(projectRoot, "specs", "verification.config.ts");
  const resultsPath = path.join(projectRoot, "specs", "tla", "generated", "tlc-output.log");

  let config: unknown = undefined;
  let lastResults: TeachingContext["verification"]["lastResults"] = undefined;

  // Try to load verification config
  if (fs.existsSync(configPath)) {
    try {
      const resolvedPath = path.resolve(configPath);
      const configModule = await import(`file://${resolvedPath}?t=${Date.now()}`);
      config = configModule.verificationConfig || configModule.default;
    } catch (error) {
      // Config exists but couldn't load - that's fine
      console.log(`Note: Could not load verification config: ${error}`);
    }
  }

  // Try to load last verification results
  if (fs.existsSync(resultsPath)) {
    try {
      const stats = fs.statSync(resultsPath);
      const output = fs.readFileSync(resultsPath, "utf-8");
      lastResults = parseVerificationResults(output, stats.mtime);
    } catch (error) {
      // Results exist but couldn't parse - that's fine
      console.log(`Note: Could not load verification results: ${error}`);
    }
  }

  if (config || lastResults) {
    return { config, lastResults };
  }

  return null;
}

function parseVerificationResults(
  output: string,
  timestamp: Date
): TeachingContext["verification"]["lastResults"] {
  const result: TeachingContext["verification"]["lastResults"] = {
    success: false,
    timestamp,
  };

  // Check for success
  if (output.includes("Model checking completed") && output.includes("No error has been found")) {
    result.success = true;

    // Extract stats
    const statesMatch = output.match(/(\d+) states generated/);
    const distinctMatch = output.match(/(\d+) distinct states/);
    if (statesMatch || distinctMatch) {
      result.stats = {
        statesGenerated: statesMatch ? Number.parseInt(statesMatch[1], 10) : 0,
        distinctStates: distinctMatch ? Number.parseInt(distinctMatch[1], 10) : 0,
      };
    }
  } else {
    // Look for violations
    const violationMatch = output.match(/Invariant (.+?) is violated/);
    if (violationMatch) {
      result.violation = {
        name: violationMatch[1],
        trace: output.split("\n").filter((line) => line.includes("State ")),
      };
    }

    // Look for errors
    const errorMatch = output.match(/Error: (.+?)$/m);
    if (errorMatch) {
      result.error = errorMatch[1];
    }
  }

  return result;
}

function findTsConfig(projectRoot: string): string | null {
  const locations = [
    path.join(projectRoot, "tsconfig.json"),
    path.join(projectRoot, "packages", "web-ext", "tsconfig.json"),
  ];

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc;
    }
  }

  return null;
}

function findStateFile(projectRoot: string): string | undefined {
  const locations = [
    path.join(projectRoot, "types", "state.ts"),
    path.join(projectRoot, "src", "types", "state.ts"),
    path.join(projectRoot, "packages", "web-ext", "src", "shared", "state", "app-state.ts"),
  ];

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc;
    }
  }

  return undefined;
}
