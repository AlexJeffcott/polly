// Types for architecture analysis (used by visualize)

import type { MessageHandler } from "./core";

// ─────────────────────────────────────────────────────────────────
// Context Information
// ─────────────────────────────────────────────────────────────────

/**
 * Information about an execution context (background, content, popup, etc.)
 */
export type ContextInfo = {
  /** Type of context */
  type: string;

  /** Entry point file path */
  entryPoint: string;

  /** Message handlers defined in this context */
  handlers: MessageHandler[];

  /** Chrome APIs used in this context */
  chromeAPIs: string[];

  /** External APIs called from this context */
  externalAPIs: ExternalAPICall[];

  /** UI components rendered (for popup/options/devtools) */
  components?: ComponentInfo[];

  /** Dependencies/imports */
  dependencies: string[];

  /** JSDoc description if available */
  description?: string;
};

/**
 * Component information (for UI contexts)
 */
export type ComponentInfo = {
  name: string;
  type: "function" | "class";
  filePath: string;
  line: number;
  props?: string[];
  description?: string;
};

// ─────────────────────────────────────────────────────────────────
// Message Flow Analysis
// ─────────────────────────────────────────────────────────────────

/**
 * Represents a message flow between contexts
 */
export type MessageFlow = {
  /** Message type identifier */
  messageType: string;

  /** Source context */
  from: string;

  /** Destination context(s) */
  to: string[];

  /** What triggers this flow (user action, event, etc.) */
  trigger?: string;

  /** Sequence of steps in this flow */
  sequence: MessageStep[];

  /** Flow name (from @flow annotation or inferred) */
  flowName?: string;

  /** Description (from JSDoc) */
  description?: string;
};

/**
 * A step in a message flow sequence
 */
export type MessageStep = {
  /** Step number in sequence */
  step: number;

  /** Action description */
  action: string;

  /** Context where this step occurs */
  context: string;

  /** Source location */
  location?: {
    file: string;
    line: number;
  };
};

// ─────────────────────────────────────────────────────────────────
// External Integrations
// ─────────────────────────────────────────────────────────────────

/**
 * External system integration
 */
export type ExternalIntegration = {
  /** Type of integration */
  type: "api" | "storage" | "browser-api" | "external-script" | "websocket";

  /** Name/identifier */
  name: string;

  /** Technology/protocol */
  technology?: string;

  /** Base URL or endpoint */
  url?: string;

  /** Where it's used (file paths) */
  usedIn: string[];

  /** Description (from JSDoc or inferred) */
  description?: string;

  /** Specific API calls made */
  calls?: ExternalAPICall[];
};

/**
 * A specific API call
 */
export type ExternalAPICall = {
  /** HTTP method or API method name */
  method: string;

  /** Endpoint or resource */
  endpoint: string;

  /** Where this call is made */
  location: {
    file: string;
    line: number;
  };

  /** Description */
  description?: string;
};

// ─────────────────────────────────────────────────────────────────
// Manifest Analysis
// ─────────────────────────────────────────────────────────────────

/**
 * Parsed manifest.json information
 */
export type ManifestInfo = {
  /** Extension name */
  name: string;

  /** Version */
  version: string;

  /** Description */
  description?: string;

  /** Manifest version (2 or 3) */
  manifestVersion: number;

  /** Background script/service worker */
  background?: {
    type: "script" | "service_worker";
    files: string[];
  };

  /** Content scripts */
  contentScripts?: Array<{
    matches: string[];
    js: string[];
    css?: string[];
  }>;

  /** Popup */
  popup?: {
    html: string;
    default?: boolean;
  };

  /** Options page */
  options?: {
    page: string;
    openInTab?: boolean;
  };

  /** DevTools page */
  devtools?: {
    page: string;
  };

  /** Permissions */
  permissions?: string[];

  /** Host permissions */
  hostPermissions?: string[];
};

// ─────────────────────────────────────────────────────────────────
// Project Configuration (Multi-Project Support)
// ─────────────────────────────────────────────────────────────────

/**
 * Project type identifier
 */
export type ProjectType =
  | "chrome-extension"
  | "pwa"
  | "websocket-app"
  | "electron"
  | "monorepo"
  | "generic";

/**
 * Project configuration with context mappings
 * Allows visualization to work with any project type
 */
export type ProjectConfig = {
  /** Type of project */
  type: ProjectType;

  /** Entry points for each context */
  entryPoints: Record<string, string>;

  /** Context type mapping (e.g., background → server, content → client) */
  contextMapping?: Record<string, string>;

  /** Workspace packages (for monorepo projects) */
  workspacePackages?: Array<{ name: string; path: string; context: string }>;

  /** Project metadata */
  metadata?: {
    name?: string;
    version?: string;
    description?: string;
  };
};

// ─────────────────────────────────────────────────────────────────
// Complete Architecture Analysis
// ─────────────────────────────────────────────────────────────────

/**
 * Complete architecture analysis result
 */
export type ArchitectureAnalysis = {
  /** Project root directory (for relative paths) */
  projectRoot: string;

  /** Basic system information */
  system: {
    name: string;
    version: string;
    description?: string;
  };

  /** Project configuration (for non-extension projects) */
  projectConfig?: ProjectConfig;

  /** Manifest information (for Chrome extensions) */
  manifest?: ManifestInfo;

  /** All contexts found in the system */
  contexts: Record<string, ContextInfo>;

  /** Message flows between contexts */
  messageFlows: MessageFlow[];

  /** External integrations */
  integrations: ExternalIntegration[];

  /** Architecture Decision Records */
  adrs?: ADRCollection;

  /** Repository information */
  repository?: {
    url: string;
    type: string;
  };
};

// Import ADR types
import type { ADRCollection } from "./adr";
