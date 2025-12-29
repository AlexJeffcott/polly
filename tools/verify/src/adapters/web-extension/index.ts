// ═══════════════════════════════════════════════════════════════
// Web Extension Adapter
// ═══════════════════════════════════════════════════════════════
//
// Extracts verification model from Chrome extension codebases.
// Recognizes:
// - Extension contexts (background, content, popup, etc.)
// - MessageBus.on() pattern for message handling
// - State mutations via state.field = value
// - Verification primitives (requires, ensures)

import { Node, Project, type SourceFile, SyntaxKind } from "ts-morph";
import type {
  CoreVerificationModel,
  MessageHandler,
  MessageType,
  NodeDefinition,
  RoutingRule,
  StateAssignment,
  VerificationCondition,
} from "../../core/model";
import type { AdapterConfig, RoutingAdapter } from "../base";

// ─────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────

/**
 * Extension contexts that can send/receive messages
 */
export type ExtensionContext =
  | "background"
  | "content"
  | "popup"
  | "devtools"
  | "options"
  | "offscreen"
  | "sidepanel";

export interface WebExtensionAdapterConfig extends AdapterConfig {
  /** Which contexts to analyze (default: all) */
  contexts?: ExtensionContext[];

  /** Whether to detect tab-based message routing */
  detectTabBased?: boolean;

  /** Maximum number of tabs to model (default: 1) */
  maxTabs?: number;

  /** Maximum messages in flight (default: 3) */
  maxInFlight?: number;
}

// ─────────────────────────────────────────────────────────────────
// Web Extension Adapter Implementation
// ─────────────────────────────────────────────────────────────────

export class WebExtensionAdapter implements RoutingAdapter<WebExtensionAdapterConfig> {
  readonly name = "web-extension";
  readonly config: WebExtensionAdapterConfig;
  private project: Project;

  constructor(config: WebExtensionAdapterConfig) {
    this.config = {
      contexts: ["background", "content", "popup", "devtools", "options", "offscreen", "sidepanel"],
      detectTabBased: true,
      maxTabs: 1,
      maxInFlight: 3,
      ...config,
    };

    this.project = new Project({
      tsConfigFilePath: config.tsConfigPath,
    });
  }

  /**
   * Extract the complete verification model from the extension codebase
   */
  extractModel(): CoreVerificationModel {
    const sourceFiles = this.project.getSourceFiles();

    // Extract all handlers
    const handlers: MessageHandler[] = [];
    const messageTypeNames = new Set<string>();

    for (const sourceFile of sourceFiles) {
      const fileHandlers = this.extractHandlersFromFile(sourceFile);
      handlers.push(...fileHandlers);

      for (const handler of fileHandlers) {
        messageTypeNames.add(handler.messageType);
      }
    }

    // Define nodes (extension contexts)
    const nodes: NodeDefinition[] = [];
    for (const context of this.config.contexts!) {
      nodes.push({
        id: context,
        type: "extension-context",
        canSendTo: ["*"], // Extensions can send to any context
        canReceiveFrom: ["*"], // Extensions can receive from any context
        metadata: {
          isServiceWorker: context === "background",
          isContentScript: context === "content",
        },
      });
    }

    // Define message types
    const messageTypes: MessageType[] = Array.from(messageTypeNames).map((name) => ({
      name,
      payload: {
        name: "unknown",
        kind: "unknown",
        nullable: false,
      },
      routing: {
        from: ["*"],
        to: ["*"],
      },
    }));

    // Define routing rules (extension uses request-reply pattern)
    const routingRules: RoutingRule[] = [
      {
        pattern: "request-reply",
        messageTypes: Array.from(messageTypeNames),
        description: "Chrome extension message passing with chrome.runtime.sendMessage",
      },
    ];

    return {
      nodes,
      messageTypes,
      routingRules,
      state: {}, // Populated by user configuration
      handlers,
      bounds: {
        maxConcurrentMessages: this.config.maxInFlight!,
        maxNodes: nodes.length,
        custom: {
          maxTabs: this.config.maxTabs!,
        },
      },
    };
  }

  /**
   * Recognize message handler registration:
   * - bus.on("TYPE", handler)
   * - chrome.runtime.onMessage.addListener(handler)
   * - browser.runtime.onMessage.addListener(handler)
   * - chrome.tabs.onUpdated.addListener(handler)
   */
  recognizeMessageHandler(node: Node): MessageHandler | null {
    if (!Node.isCallExpression(node)) {
      return null;
    }

    const expression = node.getExpression();

    // Check if this is a .on() or .addListener() call
    if (!Node.isPropertyAccessExpression(expression)) {
      return null;
    }

    const methodName = expression.getName();

    // Handle .on() pattern
    if (methodName === "on") {
      return this.extractHandlerFromOnCall(node);
    }

    // Handle .addListener() pattern (Chrome/Firefox extensions)
    if (methodName === "addListener") {
      return this.extractHandlerFromAddListener(node);
    }

    return null;
  }

  /**
   * Extract handler from .addListener() call:
   * - chrome.runtime.onMessage.addListener((message, sender, sendResponse) => { ... })
   * - chrome.tabs.onUpdated.addListener((tabId, changeInfo, tab) => { ... })
   */
  private extractHandlerFromAddListener(callExpr: Node): MessageHandler | null {
    if (!Node.isCallExpression(callExpr)) {
      return null;
    }

    const expression = callExpr.getExpression();
    if (!Node.isPropertyAccessExpression(expression)) {
      return null;
    }

    // Get the event object (e.g., chrome.runtime.onMessage, chrome.tabs.onUpdated)
    const eventObject = expression.getExpression();
    if (!Node.isPropertyAccessExpression(eventObject)) {
      return null;
    }

    // Extract event name from the property chain
    // chrome.runtime.onMessage -> "onMessage"
    // chrome.tabs.onUpdated -> "onUpdated"
    const eventName = eventObject.getName();

    // Convert event name to message type
    // onMessage -> "message"
    // onUpdated -> "updated"
    const messageType = eventName.replace(/^on/, "").toLowerCase();

    // Get the handler function (first argument)
    const args = callExpr.getArguments();
    if (args.length === 0) {
      return null;
    }

    const handlerArg = args[0];
    if (!Node.isArrowFunction(handlerArg) && !Node.isFunctionExpression(handlerArg)) {
      return null;
    }

    // Extract state mutations and conditions
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    this.extractAssignmentsFromFunction(handlerArg, assignments);
    this.extractVerificationConditionsFromFunction(handlerArg, preconditions, postconditions);

    const sourceFile = callExpr.getSourceFile();
    const line = callExpr.getStartLineNumber();

    return {
      messageType,
      node: "background", // Default, will be overridden by context inference
      assignments,
      preconditions,
      postconditions,
      location: {
        file: sourceFile.getFilePath(),
        line,
      },
    };
  }

  /**
   * Recognize state mutation: state.field = value
   */
  recognizeStateUpdate(node: Node): StateAssignment | null {
    if (!Node.isBinaryExpression(node)) {
      return null;
    }

    const operator = node.getOperatorToken().getText();
    if (operator !== "=") {
      return null;
    }

    const left = node.getLeft();
    const right = node.getRight();

    // Check if left side is a state property access
    if (!Node.isPropertyAccessExpression(left)) {
      return null;
    }

    const fieldPath = this.getPropertyPath(left);

    // Check if this is a state access
    if (!fieldPath.startsWith("state.")) {
      return null;
    }

    const field = fieldPath.substring(6); // Remove "state." prefix
    const value = this.extractValue(right);

    if (value === undefined) {
      return null;
    }

    return {
      field,
      value,
    };
  }

  /**
   * Recognize verification condition: requires() or ensures()
   */
  recognizeVerificationCondition(
    node: Node,
    type: "precondition" | "postcondition"
  ): VerificationCondition | null {
    if (!Node.isCallExpression(node)) {
      return null;
    }

    const callee = node.getExpression();
    if (!Node.isIdentifier(callee)) {
      return null;
    }

    const functionName = callee.getText();
    const expectedName = type === "precondition" ? "requires" : "ensures";

    if (functionName !== expectedName) {
      return null;
    }

    return this.extractCondition(node);
  }

  // ─────────────────────────────────────────────────────────────────
  // Private Helper Methods
  // ─────────────────────────────────────────────────────────────────

  /**
   * Extract all handlers from a source file
   */
  private extractHandlersFromFile(sourceFile: SourceFile): MessageHandler[] {
    const handlers: MessageHandler[] = [];
    const filePath = sourceFile.getFilePath();
    const context = this.inferContextFromPath(filePath);

    sourceFile.forEachDescendant((node) => {
      const handler = this.recognizeMessageHandler(node);
      if (handler) {
        // Override context with inferred value
        handlers.push({
          ...handler,
          node: context,
        });
      }
    });

    return handlers;
  }

  /**
   * Extract handler details from a .on() call expression
   */
  private extractHandlerFromOnCall(callExpr: Node): MessageHandler | null {
    if (!Node.isCallExpression(callExpr)) {
      return null;
    }

    const args = callExpr.getArguments();

    if (args.length < 2) {
      return null;
    }

    // First argument should be the message type (string literal)
    const messageTypeArg = args[0];
    let messageType: string | null = null;

    if (Node.isStringLiteral(messageTypeArg)) {
      messageType = messageTypeArg.getLiteralValue();
    } else if (Node.isTemplateExpression(messageTypeArg)) {
      messageType = messageTypeArg.getText().replace(/[`'"]/g, "");
    }

    if (!messageType) {
      return null;
    }

    // Second argument is the handler function
    const handlerArg = args[1];
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    // Parse the handler function for state assignments and verification conditions
    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      this.extractAssignmentsFromFunction(handlerArg, assignments);
      this.extractVerificationConditionsFromFunction(handlerArg, preconditions, postconditions);
    }

    const sourceFile = callExpr.getSourceFile();
    const line = callExpr.getStartLineNumber();

    return {
      messageType,
      node: "unknown", // Will be overridden by extractHandlersFromFile
      assignments,
      preconditions,
      postconditions,
      location: {
        file: sourceFile.getFilePath(),
        line,
      },
    };
  }

  /**
   * Extract state assignments from a handler function
   */
  private extractAssignmentsFromFunction(funcNode: Node, assignments: StateAssignment[]): void {
    funcNode.forEachDescendant((node) => {
      const assignment = this.recognizeStateUpdate(node);
      if (assignment) {
        assignments.push(assignment);
      }
    });
  }

  /**
   * Extract verification conditions from a handler function
   */
  private extractVerificationConditionsFromFunction(
    funcNode: Node,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    const body =
      Node.isArrowFunction(funcNode) || Node.isFunctionExpression(funcNode)
        ? funcNode.getBody()
        : funcNode;

    if (!body) {
      return;
    }

    // Get all statements in the function body
    const statements = Node.isBlock(body) ? body.getStatements() : [body];

    for (const statement of statements) {
      // Look for expression statements that are function calls
      if (Node.isExpressionStatement(statement)) {
        const expr = statement.getExpression();

        const precond = this.recognizeVerificationCondition(expr, "precondition");
        if (precond) {
          preconditions.push(precond);
        }

        const postcond = this.recognizeVerificationCondition(expr, "postcondition");
        if (postcond) {
          postconditions.push(postcond);
        }
      }
    }
  }

  /**
   * Extract condition from a requires() or ensures() call
   */
  private extractCondition(callExpr: Node): VerificationCondition | null {
    if (!Node.isCallExpression(callExpr)) {
      return null;
    }

    const args = callExpr.getArguments();

    if (args.length === 0) {
      return null;
    }

    // First argument is the condition expression
    const conditionArg = args[0];
    if (!conditionArg) return null;
    const expression = conditionArg.getText();

    // Second argument (optional) is the message
    let message: string | undefined;
    if (args.length >= 2 && Node.isStringLiteral(args[1])) {
      message = args[1].getLiteralValue();
    }

    const line = callExpr.getStartLineNumber();
    const column = callExpr.getStart();

    return {
      expression,
      message,
      location: {
        line,
        column,
      },
    };
  }

  /**
   * Get the full property access path (e.g., "state.user.loggedIn")
   */
  private getPropertyPath(node: Node): string {
    const parts: string[] = [];

    let current: Node = node;
    while (Node.isPropertyAccessExpression(current)) {
      parts.unshift(current.getName());
      current = current.getExpression();
    }

    // Add the base identifier
    if (Node.isIdentifier(current)) {
      parts.unshift(current.getText());
    }

    return parts.join(".");
  }

  /**
   * Extract a literal value from an expression
   */
  private extractValue(node: Node): string | boolean | number | null | undefined {
    if (Node.isStringLiteral(node)) {
      return node.getLiteralValue();
    }

    if (Node.isNumericLiteral(node)) {
      return node.getLiteralValue();
    }

    if (node.getKind() === SyntaxKind.TrueKeyword) {
      return true;
    }

    if (node.getKind() === SyntaxKind.FalseKeyword) {
      return false;
    }

    if (node.getKind() === SyntaxKind.NullKeyword) {
      return null;
    }

    // For complex expressions, return undefined (can't extract)
    return undefined;
  }

  /**
   * Infer the extension context from file path
   *
   * @example
   * "/src/background/index.ts" => "background"
   * "/src/popup/popup.tsx" => "popup"
   * "/src/service-worker.ts" => "Service Worker" (PWA)
   */
  private inferContextFromPath(filePath: string): string {
    const path = filePath.toLowerCase();

    // PWA service worker context
    if (path.includes("service-worker") || path.includes("sw.ts") || path.includes("sw.js")) {
      return "Service Worker";
    }

    // Chrome extension contexts
    if (path.includes("/background/") || path.includes("\\background\\")) {
      return "background";
    }
    if (path.includes("/content/") || path.includes("\\content\\")) {
      return "content";
    }
    if (path.includes("/popup/") || path.includes("\\popup\\")) {
      return "popup";
    }
    if (path.includes("/devtools/") || path.includes("\\devtools\\")) {
      return "devtools";
    }
    if (path.includes("/options/") || path.includes("\\options\\")) {
      return "options";
    }
    if (path.includes("/offscreen/") || path.includes("\\offscreen\\")) {
      return "offscreen";
    }
    if (path.includes("/sidepanel/") || path.includes("\\sidepanel\\")) {
      return "sidepanel";
    }

    return "unknown";
  }

  /**
   * Custom invariants specific to web extensions
   */
  customInvariants(): Array<[name: string, tlaExpression: string]> {
    return [
      [
        "BackgroundAlwaysConnected",
        'ports["background"] = "connected"  \\* Background context should always be available',
      ],
      [
        "ContentScriptTabBound",
        "\\A msg \\in Range(messages) : " +
          '(msg.source = "content" \\/ "content" \\in msg.targets) => msg.tabId >= 0',
      ],
    ];
  }
}
