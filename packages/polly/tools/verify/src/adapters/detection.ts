// Adapter Auto-Detection
//
// Automatically detects which adapter to use based on project structure,
// dependencies, and code patterns.

import type { SourceFile } from "typescript-7/ast";
import { readString } from "../../../../src/shared/lib/guards";
import {
  type AnalysisProgram,
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
    const sourceFiles = program.sourceFiles;
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
    let chromeApiCount = 0;
    for (const file of files) {
      const text = file.text;
      if (text.includes("chrome.runtime") || text.includes("chrome.tabs")) {
        chromeApiCount++;
      }
    }
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
    let messageBusCount = 0;
    for (const file of files) {
      const text = file.text;
      if (text.includes("MessageBus") || text.includes("getMessageBus")) {
        messageBusCount++;
      }
    }
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
    const emitterOnCount = this.countPatternMatches(files, /\.on\s*\(\s*['"`]/g);
    if (emitterOnCount > 0) {
      confidence += Math.min(30, emitterOnCount * 5);
      evidence.push(`Found ${emitterOnCount} .on() call(s)`);
    }

    // Check for emitter.emit() pattern
    const emitterEmitCount = this.countPatternMatches(files, /\.emit\s*\(\s*['"`]/g);
    if (emitterEmitCount > 0) {
      confidence += Math.min(30, emitterEmitCount * 3);
      evidence.push(`Found ${emitterEmitCount} .emit() call(s)`);
    }

    // Penalty if chrome APIs are present (likely not pure event bus)
    const chromeApiCount = this.countChromeAPIUsage(files);
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
   * Count pattern matches across files
   */
  private countPatternMatches(files: readonly SourceFile[], pattern: RegExp): number {
    let count = 0;
    for (const file of files) {
      const text = file.text;
      const matches = text.match(pattern);
      if (matches) {
        count += matches.length;
      }
    }
    return count;
  }

  /**
   * Count Chrome API usage across files
   */
  private countChromeAPIUsage(files: readonly SourceFile[]): number {
    let count = 0;
    for (const file of files) {
      if (file.text.includes("chrome.runtime")) {
        count++;
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
    let workerCount = 0;
    for (const file of files) {
      const text = file.text;
      if (text.includes("new Worker(") || text.includes("new SharedWorker(")) {
        workerCount++;
      }
    }
    if (workerCount > 0) {
      confidence += Math.min(40, workerCount * 20);
      evidence.push(`Found ${workerCount} Worker instantiation(s)`);
    }

    // Check for postMessage usage
    let postMessageCount = 0;
    for (const file of files) {
      const text = file.text;
      const matches = text.match(/\.postMessage\s*\(/g);
      if (matches) {
        postMessageCount += matches.length;
      }
    }
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

/**
 * Detect the most appropriate adapter for a project
 */
export function detectAdapter(
  tsConfigPath: string,
  source?: AnalysisSource
): Promise<AdapterDetectionResult> {
  return new AdapterDetector(tsConfigPath).detect(source);
}
