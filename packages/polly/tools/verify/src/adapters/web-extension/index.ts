// Web Extension Adapter
//
// Extracts verification model from Chrome extension codebases.
// Recognizes:
// - Extension contexts (background, content, popup, etc.)
// - MessageBus.on() pattern for message handling
// - State mutations via state.field = value
// - Verification primitives (requires, ensures)

import {
  type Node,
  type ObjectLiteralExpression,
  type SourceFile,
  SyntaxKind,
} from "typescript-7/ast";
import {
  isArrowFunction,
  isBinaryExpression,
  isBlock,
  isCallExpression,
  isExpressionStatement,
  isFunctionExpression,
  isIdentifier,
  isNumericLiteral,
  isObjectLiteralExpression,
  isPropertyAccessExpression,
  isPropertyAssignment,
  isStringLiteral,
  isTemplateExpression,
} from "typescript-7/ast/is";
import {
  type AnalysisProgram,
  forEachDescendant,
  literalValue,
  nameOf,
  startLine,
  startOf,
  textOf,
} from "../../../../analysis/src/program";
import type {
  CoreVerificationModel,
  MessageHandler,
  MessageType,
  NodeDefinition,
  RoutingRule,
  StateAssignment,
  StateConstraint,
  VerificationCondition,
} from "../../core/model";
import { type AnalysisSource, withAdapterProgram } from "../analysis-source";
import type { AdapterConfig, RoutingAdapter } from "../base";

// Configuration

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

// Web Extension Adapter Implementation

export class WebExtensionAdapter implements RoutingAdapter<WebExtensionAdapterConfig> {
  readonly name = "web-extension";
  readonly config: WebExtensionAdapterConfig;

  constructor(config: WebExtensionAdapterConfig) {
    this.config = {
      contexts: ["background", "content", "popup", "devtools", "options", "offscreen", "sidepanel"],
      detectTabBased: true,
      maxTabs: 1,
      maxInFlight: 3,
      ...config,
    };
  }

  /**
   * Extract the complete verification model from the extension codebase
   */
  extractModel(source?: AnalysisSource): Promise<CoreVerificationModel> {
    return withAdapterProgram(this.config.tsConfigPath, source, (program) =>
      this.extractModelFrom(program)
    );
  }

  private extractModelFrom(program: AnalysisProgram): CoreVerificationModel {
    const sourceFiles = program.sourceFiles;

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

    // Extract state-level constraints
    const stateConstraints: StateConstraint[] = [];
    for (const sourceFile of sourceFiles) {
      const fileConstraints = this.extractStateConstraintsFromFile(sourceFile);
      stateConstraints.push(...fileConstraints);
    }

    // Define nodes (extension contexts)
    const nodes: NodeDefinition[] = [];
    const contexts = this.config.contexts ?? [
      "background",
      "content",
      "popup",
      "devtools",
      "options",
      "offscreen",
      "sidepanel",
    ];
    for (const context of contexts) {
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
      stateConstraints,
      bounds: {
        maxConcurrentMessages: this.config.maxInFlight ?? 3,
        maxNodes: nodes.length,
        custom: {
          maxTabs: this.config.maxTabs ?? 1,
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
    if (!isCallExpression(node)) {
      return null;
    }

    const expression = node.expression;

    // Check if this is a .on() or .addListener() call
    if (!isPropertyAccessExpression(expression)) {
      return null;
    }

    const methodName = nameOf(expression);

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
    if (!isCallExpression(callExpr)) {
      return null;
    }

    const expression = callExpr.expression;
    if (!isPropertyAccessExpression(expression)) {
      return null;
    }

    // Get the event object (e.g., chrome.runtime.onMessage, chrome.tabs.onUpdated)
    const eventObject = expression.expression;
    if (!isPropertyAccessExpression(eventObject)) {
      return null;
    }

    // Extract event name from the property chain
    // chrome.runtime.onMessage -> "onMessage"
    // chrome.tabs.onUpdated -> "onUpdated"
    const eventName = textOf(eventObject.name);

    // Convert event name to message type
    // onMessage -> "message"
    // onUpdated -> "updated"
    const messageType = eventName.replace(/^on/, "").toLowerCase();

    // Get the handler function (first argument)
    const args = callExpr.arguments;
    if (args.length === 0) {
      return null;
    }

    const handlerArg = args[0];
    if (!handlerArg || (!isArrowFunction(handlerArg) && !isFunctionExpression(handlerArg))) {
      return null;
    }

    // Extract state mutations and conditions
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    this.extractAssignmentsFromFunction(handlerArg, assignments);
    this.extractVerificationConditionsFromFunction(handlerArg, preconditions, postconditions);

    const sourceFile = callExpr.getSourceFile();
    const line = startLine(callExpr);

    return {
      messageType,
      node: "background", // Default, will be overridden by context inference
      assignments,
      preconditions,
      postconditions,
      location: {
        file: sourceFile.fileName,
        line,
      },
    };
  }

  /**
   * Recognize state mutation: state.field = value OR signalName.value = expression
   */
  recognizeStateUpdate(node: Node): StateAssignment | null {
    if (!isBinaryExpression(node)) {
      return null;
    }

    if (node.operatorToken.kind !== SyntaxKind.EqualsToken) {
      return null;
    }

    const left = node.left;
    const right = node.right;

    // Check if left side is a state property access
    if (!isPropertyAccessExpression(left)) {
      return null;
    }

    const fieldPath = this.getPropertyPath(left);

    // Pattern 1: state.field = value (explicit state object)
    if (fieldPath.startsWith("state.")) {
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

    // Pattern 2: signalName.value = expression (signal pattern)
    if (fieldPath.endsWith(".value")) {
      const signalName = fieldPath.slice(0, -6); // Remove ".value" suffix
      return this.extractSignalAssignment(signalName, right);
    }

    return null;
  }

  /**
   * Extract state assignment from signal pattern: signalName.value = expression
   * Handles both simple literals and object literal expressions
   */
  private extractSignalAssignment(signalName: string, right: Node): StateAssignment | null {
    // Case 1: Simple literal assignment (e.g., user.value = true)
    const simpleValue = this.extractValue(right);
    if (simpleValue !== undefined) {
      return { field: signalName, value: simpleValue };
    }

    // Case 2: Object literal - extract first extractable property as state field
    // e.g., user.value = { loggedIn: true } -> user_loggedIn = true
    if (isObjectLiteralExpression(right)) {
      return this.extractFirstObjectProperty(signalName, right);
    }

    // Can't extract complex expressions (arrays, spreads, function calls, etc.)
    return null;
  }

  /**
   * Extract first extractable property from object literal
   */
  private extractFirstObjectProperty(
    signalName: string,
    objectLiteral: ObjectLiteralExpression
  ): StateAssignment | null {
    for (const prop of objectLiteral.properties) {
      if (!isPropertyAssignment(prop)) continue;

      const propName = textOf(prop.name);
      const initializer = prop.initializer;
      if (!initializer) continue;

      const propValue = this.extractValue(initializer);
      if (propValue === undefined) continue;

      // Combine signal name with property: user + loggedIn -> user_loggedIn
      return { field: `${signalName}_${propName}`, value: propValue };
    }
    return null;
  }

  /**
   * Recognize verification condition: requires() or ensures()
   */
  recognizeVerificationCondition(
    node: Node,
    type: "precondition" | "postcondition"
  ): VerificationCondition | null {
    if (!isCallExpression(node)) {
      return null;
    }

    const callee = node.expression;
    if (!isIdentifier(callee)) {
      return null;
    }

    const functionName = textOf(callee);
    const expectedName = type === "precondition" ? "requires" : "ensures";

    if (functionName !== expectedName) {
      return null;
    }

    return this.extractCondition(node);
  }

  // Private Helper Methods

  /**
   * Extract all handlers from a source file
   */
  private extractHandlersFromFile(sourceFile: SourceFile): MessageHandler[] {
    const handlers: MessageHandler[] = [];
    const filePath = sourceFile.fileName;
    const context = this.inferContextFromPath(filePath);

    forEachDescendant(sourceFile, (node) => {
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
   * Extract state-level constraints from a source file
   */
  private extractStateConstraintsFromFile(sourceFile: SourceFile): StateConstraint[] {
    const constraints: StateConstraint[] = [];
    const filePath = sourceFile.fileName;

    forEachDescendant(sourceFile, (node) => {
      const nodeConstraints = this.recognizeStateConstraint(node);
      if (nodeConstraints.length > 0) {
        for (const constraint of nodeConstraints) {
          constraints.push({
            ...constraint,
            location: {
              ...constraint.location,
              file: filePath,
            },
          });
        }
      }
    });

    return constraints;
  }

  /**
   * Recognize a $constraints() call and extract constraint definitions
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Parser logic requires nested conditionals
  private recognizeStateConstraint(node: Node): StateConstraint[] {
    if (!isCallExpression(node)) {
      return [];
    }

    const expression = node.expression;
    if (!isIdentifier(expression)) {
      return [];
    }

    const functionName = textOf(expression);
    if (functionName !== "$constraints") {
      return [];
    }

    // Get arguments: $constraints(field, constraintsObject)
    const args = node.arguments;
    if (args.length < 2) {
      return [];
    }

    // First argument is the state field name
    const fieldArg = args[0];
    if (!fieldArg || !isStringLiteral(fieldArg)) {
      return [];
    }
    const field = literalValue(fieldArg);

    // Second argument is the constraints object
    const constraintsArg = args[1];
    if (!constraintsArg || !isObjectLiteralExpression(constraintsArg)) {
      return [];
    }

    // Extract each message type constraint
    const results: StateConstraint[] = [];
    for (const property of constraintsArg.properties) {
      if (!isPropertyAssignment(property)) {
        continue;
      }

      const messageType = textOf(property.name);
      const initializer = property.initializer;
      if (!initializer || !isObjectLiteralExpression(initializer)) {
        continue;
      }

      // Extract requires, ensures, and message from the constraint object
      let requires: string | undefined;
      let ensures: string | undefined;
      let message: string | undefined;

      for (const constraintProp of initializer.properties) {
        if (!isPropertyAssignment(constraintProp)) {
          continue;
        }

        const propName = textOf(constraintProp.name);
        const propValue = constraintProp.initializer;
        if (!propValue) {
          continue;
        }

        if (propName === "requires" && isStringLiteral(propValue)) {
          requires = literalValue(propValue);
        } else if (propName === "ensures" && isStringLiteral(propValue)) {
          ensures = literalValue(propValue);
        } else if (propName === "message" && isStringLiteral(propValue)) {
          message = literalValue(propValue);
        }
      }

      results.push({
        field,
        messageType,
        requires,
        ensures,
        message,
        location: {
          file: "", // Will be set by caller
          line: startLine(property),
        },
      });
    }

    // Return all extracted constraints
    return results;
  }

  /**
   * Extract handler details from a .on() call expression
   */
  private extractHandlerFromOnCall(callExpr: Node): MessageHandler | null {
    if (!isCallExpression(callExpr)) {
      return null;
    }

    const args = callExpr.arguments;

    if (args.length < 2) {
      return null;
    }

    // First argument should be the message type (string literal)
    const messageTypeArg = args[0];
    let messageType: string | null = null;

    if (messageTypeArg && isStringLiteral(messageTypeArg)) {
      messageType = literalValue(messageTypeArg);
    } else if (messageTypeArg && isTemplateExpression(messageTypeArg)) {
      messageType = textOf(messageTypeArg).replace(/[`'"]/g, "");
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
    if (handlerArg && (isArrowFunction(handlerArg) || isFunctionExpression(handlerArg))) {
      this.extractAssignmentsFromFunction(handlerArg, assignments);
      this.extractVerificationConditionsFromFunction(handlerArg, preconditions, postconditions);
    }

    const sourceFile = callExpr.getSourceFile();
    const line = startLine(callExpr);

    return {
      messageType,
      node: "unknown", // Will be overridden by extractHandlersFromFile
      assignments,
      preconditions,
      postconditions,
      location: {
        file: sourceFile.fileName,
        line,
      },
    };
  }

  /**
   * Extract state assignments from a handler function
   */
  private extractAssignmentsFromFunction(funcNode: Node, assignments: StateAssignment[]): void {
    forEachDescendant(funcNode, (node) => {
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
      isArrowFunction(funcNode) || isFunctionExpression(funcNode) ? funcNode.body : funcNode;

    if (!body) {
      return;
    }

    // Get all statements in the function body
    const statements = isBlock(body) ? body.statements : [body];

    for (const statement of statements) {
      // Look for expression statements that are function calls
      if (isExpressionStatement(statement)) {
        const expr = statement.expression;

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
    if (!isCallExpression(callExpr)) {
      return null;
    }

    const args = callExpr.arguments;

    if (args.length === 0) {
      return null;
    }

    // First argument is the condition expression
    const conditionArg = args[0];
    if (!conditionArg) return null;
    const expression = textOf(conditionArg);

    // Second argument (optional) is the message
    let message: string | undefined;
    const messageArg = args[1];
    if (messageArg && isStringLiteral(messageArg)) {
      message = literalValue(messageArg);
    }

    const line = startLine(callExpr);
    const column = startOf(callExpr);

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
    while (isPropertyAccessExpression(current)) {
      parts.unshift(textOf(current.name));
      current = current.expression;
    }

    // Add the base identifier
    if (isIdentifier(current)) {
      parts.unshift(textOf(current));
    }

    return parts.join(".");
  }

  /**
   * Extract a literal value from an expression
   */
  private extractValue(node: Node): string | boolean | number | null | undefined {
    if (isStringLiteral(node)) {
      return literalValue(node);
    }

    if (isNumericLiteral(node)) {
      return literalValue(node);
    }

    if (node.kind === SyntaxKind.TrueKeyword) {
      return true;
    }

    if (node.kind === SyntaxKind.FalseKeyword) {
      return false;
    }

    if (node.kind === SyntaxKind.NullKeyword) {
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
    if (this.isServiceWorkerPath(path)) {
      return "Service Worker";
    }

    // Chrome extension contexts
    const contexts = [
      "background",
      "content",
      "popup",
      "devtools",
      "options",
      "offscreen",
      "sidepanel",
    ];
    for (const context of contexts) {
      if (this.pathMatchesContext(path, context)) {
        return context;
      }
    }

    return "unknown";
  }

  /**
   * Check if path is a service worker
   */
  private isServiceWorkerPath(path: string): boolean {
    return path.includes("service-worker") || path.includes("sw.ts") || path.includes("sw.js");
  }

  /**
   * Check if path matches a context directory
   */
  private pathMatchesContext(path: string, context: string): boolean {
    return path.includes(`/${context}/`) || path.includes(`\\${context}\\`);
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
