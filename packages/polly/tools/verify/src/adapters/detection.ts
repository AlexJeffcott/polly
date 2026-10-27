// Adapter Auto-Detection
//
// Automatically detects which adapter to use based on project structure,
// dependencies, and code patterns.

import type { Node, SourceFile } from "typescript-7/ast";
import {
  isCallExpression,
  isIdentifier,
  isNewExpression,
  isNoSubstitutionTemplateLiteral,
  isPropertyAccessExpression,
  isStringLiteral,
  isTemplateExpression,
} from "typescript-7/ast/is";
import { readString } from "../../../../src/shared/lib/guards";
import {
  type AnalysisProgram,
  forEachDescendant,
  importDeclarations,
  moduleSpecifierValue,
} from "../../../analysis/src/program";
import { type AnalysisSource, withAdapterProgram } from "./analysis-source";
import type { RoutingAdapter } from "./base";
import { EventBusAdapter } from "./event-bus";
import { WebExtensionAdapter } from "./web-extension";

// Detection Result

export interface AdapterDetectionResult {
  /** The recommended adapter type */
  adapterType: "web-extension" | "event-bus" | "worker" | "unknown";

  /** Confidence level (0-100) */
  confidence: number;

  /** Evidence supporting this detection */
  evidence: string[];

  /** Suggested adapter configuration */
  suggestedAdapter?: RoutingAdapter;

  /** Alternative adapters that might also work */
  alternatives?: Array<{
    adapterType: string;
    confidence: number;
    evidence: string[];
  }>;
}

// Adapter Detector

export class AdapterDetector {
  private readonly tsConfigPath: string;

  constructor(tsConfigPath: string) {
    this.tsConfigPath = tsConfigPath;
  }

  /**
   * Detect the most appropriate adapter for this project
   *
   * @param source - A session (the tsconfig is opened in it) or an open
   *   program; the caller keeps ownership. Omitted, a session is opened for
   *   this call and closed before it returns.
   */
  detect(source?: AnalysisSource): Promise<AdapterDetectionResult> {
    return withAdapterProgram(this.tsConfigPath, source, (program) => this.detectIn(program));
  }

  private detectIn(program: AnalysisProgram): AdapterDetectionResult {
    // The project's own code only. Declaration files are other packages'
    // types: polly's dist/*.d.ts declares MessageBus and documents chrome.*,
    // and @types/chrome declares every chrome namespace.
    const sourceFiles = program.sourceFiles.filter((file) => !file.isDeclarationFile);
    const tsConfigPath = readString(program.compilerOptions.configFilePath) || "tsconfig.json";

    // Run all detection heuristics
    const webExtensionScore = this.detectWebExtension(sourceFiles);
    const eventBusScore = this.detectEventBus(sourceFiles);
    const workerScore = this.detectWorker(sourceFiles);

    // Determine the best match
    const scores = [
      { type: "web-extension" as const, ...webExtensionScore },
      { type: "event-bus" as const, ...eventBusScore },
      { type: "worker" as const, ...workerScore },
    ].sort((a, b) => b.confidence - a.confidence);

    const best = scores[0];
    if (!best) {
      throw new Error("No adapter scores available");
    }
    const alternatives = scores.slice(1).filter((s) => s.confidence > 20);

    // Create suggested adapter for the best match
    let suggestedAdapter: RoutingAdapter | undefined;
    if (best.confidence > 50) {
      if (best.type === "web-extension") {
        suggestedAdapter = new WebExtensionAdapter({
          tsConfigPath,
          maxInFlight: 6,
          maxTabs: 2,
        });
      } else if (best.type === "event-bus") {
        suggestedAdapter = new EventBusAdapter({
          tsConfigPath,
          maxInFlight: 5,
        });
      }
    }

    return {
      adapterType: best.confidence > 30 ? best.type : "unknown",
      confidence: best.confidence,
      evidence: best.evidence,
      suggestedAdapter,
      alternatives: alternatives.map((a) => ({
        adapterType: a.type,
        confidence: a.confidence,
        evidence: a.evidence,
      })),
    };
  }

  // Detection Heuristics

  /**
   * Detect web extension patterns
   */
  private detectWebExtension(files: readonly SourceFile[]): {
    confidence: number;
    evidence: string[];
  } {
    let confidence = 0;
    const evidence: string[] = [];

    // Check for manifest.json
    const hasManifest = files.some((f) => f.fileName.includes("manifest.json"));
    if (hasManifest) {
      confidence += 30;
      evidence.push("Found manifest.json");
    }

    // Check for chrome API imports
    const chromeApiCount = filesWith(files, chromeApi("runtime", "tabs"));
    if (chromeApiCount > 0) {
      confidence += Math.min(30, chromeApiCount * 10);
      evidence.push(`Found ${chromeApiCount} file(s) using chrome.* APIs`);
    }

    // Check for extension directories
    const hasBackground = files.some((f) => f.fileName.includes("/background/"));
    const hasContent = files.some((f) => f.fileName.includes("/content/"));
    const hasPopup = files.some((f) => f.fileName.includes("/popup/"));

    const contextCount = [hasBackground, hasContent, hasPopup].filter(Boolean).length;
    if (contextCount > 0) {
      confidence += contextCount * 15;
      evidence.push(`Found ${contextCount} extension context directories`);
    }

    // Check for MessageBus usage
    const messageBusCount = filesWith(
      files,
      (node) => isIdentifier(node) && (node.text === "MessageBus" || node.text === "getMessageBus")
    );
    if (messageBusCount > 0) {
      confidence += Math.min(20, messageBusCount * 5);
      evidence.push(`Found ${messageBusCount} file(s) using MessageBus`);
    }

    return { confidence: Math.min(100, confidence), evidence };
  }

  /**
   * Detect event bus patterns
   */
  private detectEventBus(files: readonly SourceFile[]): { confidence: number; evidence: string[] } {
    let confidence = 0;
    const evidence: string[] = [];

    // Check for EventEmitter imports
    const eventEmitterImports = this.countEventEmitterImports(files);
    if (eventEmitterImports > 0) {
      confidence += Math.min(40, eventEmitterImports * 15);
      evidence.push(`Found ${eventEmitterImports} EventEmitter import(s)`);
    }

    // Check for emitter.on() pattern
    const emitterOnCount = countNodes(files, methodCall("on", { stringFirstArg: true }));
    if (emitterOnCount > 0) {
      confidence += Math.min(30, emitterOnCount * 5);
      evidence.push(`Found ${emitterOnCount} .on() call(s)`);
    }

    // Check for emitter.emit() pattern
    const emitterEmitCount = countNodes(files, methodCall("emit", { stringFirstArg: true }));
    if (emitterEmitCount > 0) {
      confidence += Math.min(30, emitterEmitCount * 3);
      evidence.push(`Found ${emitterEmitCount} .emit() call(s)`);
    }

    // Penalty if chrome APIs are present (likely not pure event bus)
    const chromeApiCount = filesWith(files, chromeApi("runtime"));
    if (chromeApiCount > 5) {
      confidence = Math.max(0, confidence - 20);
      evidence.push("Note: Also found Chrome APIs (might be extension)");
    }

    return { confidence: Math.min(100, confidence), evidence };
  }

  /**
   * Count EventEmitter imports across files
   */
  private countEventEmitterImports(files: readonly SourceFile[]): number {
    let count = 0;
    for (const file of files) {
      for (const imp of importDeclarations(file)) {
        const module = moduleSpecifierValue(imp);
        if (module === "events" || module === "eventemitter3" || module === "mitt") {
          count++;
        }
      }
    }
    return count;
  }

  /**
   * Detect web worker patterns
   */
  private detectWorker(files: readonly SourceFile[]): { confidence: number; evidence: string[] } {
    let confidence = 0;
    const evidence: string[] = [];

    // Check for Worker usage
    const workerCount = filesWith(
      files,
      (node) =>
        isNewExpression(node) &&
        isIdentifier(node.expression) &&
        (node.expression.text === "Worker" || node.expression.text === "SharedWorker")
    );
    if (workerCount > 0) {
      confidence += Math.min(40, workerCount * 20);
      evidence.push(`Found ${workerCount} Worker instantiation(s)`);
    }

    // Check for postMessage usage
    const postMessageCount = countNodes(files, methodCall("postMessage"));
    if (postMessageCount > 0) {
      confidence += Math.min(30, postMessageCount * 5);
      evidence.push(`Found ${postMessageCount} .postMessage() call(s)`);
    }

    // Check for worker directories
    const hasWorkerDir = files.some(
      (f) => f.fileName.includes("/worker/") || f.fileName.includes("/workers/")
    );
    if (hasWorkerDir) {
      confidence += 20;
      evidence.push("Found worker directory");
    }

    return { confidence: Math.min(100, confidence), evidence };
  }
}

// Syntax-tree matching. The heuristics matched regexes over the file text, so a
// comment or a string such as `// bus.on("X")` counted as a call. Comments are
// trivia, not nodes, and a string is one literal node.

type NodeMatch = (node: Node) => boolean;

/** Nodes that match, over every file. */
function countNodes(files: readonly SourceFile[], match: NodeMatch): number {
  let count = 0;
  for (const file of files) {
    forEachDescendant(file, (node) => {
      if (match(node)) count++;
      return undefined;
    });
  }
  return count;
}

/** Files with at least one node that matches. */
function filesWith(files: readonly SourceFile[], match: NodeMatch): number {
  return files.filter((file) => forEachDescendant(file, (node) => match(node) || undefined)).length;
}

/** `x.method(...)`; with `stringFirstArg`, only when the first argument is a string or template. */
function methodCall(method: string, opts: { stringFirstArg?: boolean } = {}): NodeMatch {
  return (node) => {
    if (!isCallExpression(node)) return false;
    const callee = node.expression;
    if (!isPropertyAccessExpression(callee) || callee.name.text !== method) return false;
    if (!opts.stringFirstArg) return true;
    const first = node.arguments[0];
    return (
      first !== undefined &&
      (isStringLiteral(first) ||
        isNoSubstitutionTemplateLiteral(first) ||
        isTemplateExpression(first))
    );
  };
}

/** `chrome.<namespace>` for any of the namespaces. */
function chromeApi(...namespaces: string[]): NodeMatch {
  return (node) =>
    isPropertyAccessExpression(node) &&
    isIdentifier(node.expression) &&
    node.expression.text === "chrome" &&
    namespaces.includes(node.name.text);
}

/**
 * Detect the most appropriate adapter for a project
 */
export function detectAdapter(
  tsConfigPath: string,
  source?: AnalysisSource
): Promise<AdapterDetectionResult> {
  return new AdapterDetector(tsConfigPath).detect(source);
}
