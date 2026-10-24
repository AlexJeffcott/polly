// Event Bus Adapter
//
// Extracts verification model from event-driven systems using EventEmitter.
// Recognizes:
// - EventEmitter instances (Node.js EventEmitter, mitt, etc.)
// - emitter.on(event, handler) pattern
// - emitter.emit(event, data) pattern
// - State mutations via state.field = value
// - Verification primitives (requires, ensures)

import { type Node, type SourceFile, SyntaxKind } from "typescript-7/ast";
import {
  isArrowFunction,
  isBinaryExpression,
  isBlock,
  isCallExpression,
  isExpressionStatement,
  isFunctionExpression,
  isIdentifier,
  isNumericLiteral,
  isPropertyAccessExpression,
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
  VerificationCondition,
} from "../../core/model";
import { type AnalysisSource, withAdapterProgram } from "../analysis-source";
import type { AdapterConfig, RoutingAdapter } from "../base";

// Configuration

export interface EventBusAdapterConfig extends AdapterConfig {
  /** EventEmitter library being used (default: "events") */
  emitterLibrary?: "events" | "mitt" | "eventemitter3" | "custom";

  /** Pattern to match emitter instances (default: /emitter|bus|events/i) */
  emitterPattern?: RegExp;

  /** Maximum concurrent events to model (default: 5) */
  maxInFlight?: number;

  /** Maximum number of emitter instances (default: 3) */
  maxEmitters?: number;
}

// Event Bus Adapter Implementation

export class EventBusAdapter implements RoutingAdapter<EventBusAdapterConfig> {
  readonly name = "event-bus";
  readonly config: EventBusAdapterConfig;

  constructor(config: EventBusAdapterConfig) {
    this.config = {
      emitterLibrary: "events",
      emitterPattern: /emitter|bus|events/i,
      maxInFlight: 5,
      maxEmitters: 3,
      ...config,
    };
  }

  /**
   * Extract the complete verification model from the event-driven codebase
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
    const emitterNames = new Set<string>();

    for (const sourceFile of sourceFiles) {
      const fileHandlers = this.extractHandlersFromFile(sourceFile);
      handlers.push(...fileHandlers);

      for (const handler of fileHandlers) {
        messageTypeNames.add(handler.messageType);
        emitterNames.add(handler.node);
      }
    }

    // Define nodes (emitters)
    const nodes: NodeDefinition[] = [];

    // Central event bus node (mediator pattern)
    nodes.push({
      id: "central-bus",
      type: "event-bus",
      canSendTo: ["*"],
      canReceiveFrom: ["*"],
      metadata: {
        isMediator: true,
      },
    });

    // Individual emitter nodes
    for (const emitterName of emitterNames) {
      if (emitterName !== "central-bus") {
        nodes.push({
          id: emitterName,
          type: "emitter",
          canSendTo: ["central-bus", "*"],
          canReceiveFrom: ["central-bus", "*"],
          metadata: {
            isEmitter: true,
          },
        });
      }
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

    // Define routing rules (event bus uses broadcast pattern)
    const routingRules: RoutingRule[] = [
      {
        pattern: "broadcast",
        messageTypes: Array.from(messageTypeNames),
        description: "Event bus broadcast pattern - one-to-many messaging",
      },
    ];

    return {
      nodes,
      messageTypes,
      routingRules,
      state: {}, // Populated by user configuration
      handlers,
      stateConstraints: [], // This adapter recognises no $constraints declarations
      bounds: {
        maxConcurrentMessages: this.config.maxInFlight ?? 5,
        maxNodes: Math.min(nodes.length, (this.config.maxEmitters ?? 3) + 1), // +1 for central bus
      },
    };
  }

  /**
   * Recognize message handler registration: emitter.on("event", handler)
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
    if (methodName !== "on" && methodName !== "addListener" && methodName !== "addEventListener") {
      return null;
    }

    return this.extractHandlerFromOnCall(node);
  }

  /**
   * Recognize state mutation: state.field = value
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
    const contextFromPath = this.inferContextFromPath(filePath);

    forEachDescendant(sourceFile, (node) => {
      const handler = this.recognizeMessageHandler(node);
      if (handler) {
        // Override node with context inferred from file path if available
        if (contextFromPath === "unknown") {
          handlers.push(handler);
        } else {
          handlers.push({
            ...handler,
            node: contextFromPath,
          });
        }
      }
    });

    return handlers;
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

    // First argument should be the event name (string literal)
    const eventNameArg = args[0];
    let eventName: string | null = null;

    if (eventNameArg && isStringLiteral(eventNameArg)) {
      eventName = literalValue(eventNameArg);
    } else if (eventNameArg && isTemplateExpression(eventNameArg)) {
      eventName = textOf(eventNameArg).replace(/[`'"]/g, "");
    }

    if (!eventName) {
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

    // Infer emitter name from the call expression
    const expression = callExpr.expression;
    let emitterName = "central-bus";
    if (isPropertyAccessExpression(expression)) {
      const emitterExpr = expression.expression;
      if (isIdentifier(emitterExpr)) {
        emitterName = textOf(emitterExpr);
      }
    }

    // Check if emitter name matches the pattern
    if (!this.config.emitterPattern?.test(emitterName)) {
      return null; // Emitter doesn't match pattern, skip this handler
    }

    const sourceFile = callExpr.getSourceFile();
    const line = startLine(callExpr);

    return {
      messageType: eventName,
      node: emitterName,
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
   * Infer execution context from file path
   *
   * @example
   * "/src/main.ts" => "Main Process" (Electron)
   * "/src/renderer/index.ts" => "Renderer" (Electron)
   * "/src/preload.ts" => "Preload" (Electron)
   */
  private inferContextFromPath(filePath: string): string {
    const path = filePath.toLowerCase();

    // Electron main process
    if (
      path.includes("main.ts") ||
      path.includes("main.js") ||
      path.includes("/main/") ||
      path.includes("\\main\\")
    ) {
      return "Main Process";
    }

    // Electron renderer process
    if (
      path.includes("/renderer/") ||
      path.includes("\\renderer\\") ||
      path.includes("renderer.ts") ||
      path.includes("renderer.js")
    ) {
      return "Renderer";
    }

    // Electron preload script
    if (path.includes("preload.ts") || path.includes("preload.js")) {
      return "Preload";
    }

    return "unknown";
  }

  /**
   * Custom invariants specific to event buses
   */
  customInvariants(): Array<[name: string, tlaExpression: string]> {
    return [
      [
        "CentralBusAlwaysAvailable",
        'ports["central-bus"] = "connected"  \\* Central event bus should always be available',
      ],
      [
        "BroadcastOrdering",
        "\\A msg1, msg2 \\in Range(messages) : " +
          '(msg1.msgType = msg2.msgType /\\ msg1.status = "delivered" /\\ msg2.status = "pending") => ' +
          "msg1.id < msg2.id  \\* Events of the same type are delivered in order",
      ],
    ];
  }
}
