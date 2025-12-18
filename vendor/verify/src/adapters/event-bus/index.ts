// ═══════════════════════════════════════════════════════════════
// Event Bus Adapter
// ═══════════════════════════════════════════════════════════════
//
// Extracts verification model from event-driven systems using EventEmitter.
// Recognizes:
// - EventEmitter instances (Node.js EventEmitter, mitt, etc.)
// - emitter.on(event, handler) pattern
// - emitter.emit(event, data) pattern
// - State mutations via state.field = value
// - Verification primitives (requires, ensures)

import { Project, type SourceFile, SyntaxKind, Node } from "ts-morph";
import type {
  CoreVerificationModel,
  MessageHandler,
  StateAssignment,
  VerificationCondition,
  NodeDefinition,
  MessageType,
  RoutingRule,
} from "../../core/model";
import type { AdapterConfig, RoutingAdapter } from "../base";

// ─────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────

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

// ─────────────────────────────────────────────────────────────────
// Event Bus Adapter Implementation
// ─────────────────────────────────────────────────────────────────

export class EventBusAdapter implements RoutingAdapter<EventBusAdapterConfig> {
  readonly name = "event-bus";
  readonly config: EventBusAdapterConfig;
  private project: Project;

  constructor(config: EventBusAdapterConfig) {
    this.config = {
      emitterLibrary: "events",
      emitterPattern: /emitter|bus|events/i,
      maxInFlight: 5,
      maxEmitters: 3,
      ...config,
    };

    this.project = new Project({
      tsConfigFilePath: config.tsConfigPath,
    });
  }

  /**
   * Extract the complete verification model from the event-driven codebase
   */
  extractModel(): CoreVerificationModel {
    const sourceFiles = this.project.getSourceFiles();

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
      bounds: {
        maxConcurrentMessages: this.config.maxInFlight!,
        maxNodes: Math.min(nodes.length, this.config.maxEmitters! + 1), // +1 for central bus
      },
    };
  }

  /**
   * Recognize message handler registration: emitter.on("event", handler)
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
    if (methodName !== "on" && methodName !== "addListener" && methodName !== "addEventListener") {
      return null;
    }

    return this.extractHandlerFromOnCall(node);
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

    sourceFile.forEachDescendant((node) => {
      const handler = this.recognizeMessageHandler(node);
      if (handler) {
        handlers.push(handler);
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

    // First argument should be the event name (string literal)
    const eventNameArg = args[0];
    let eventName: string | null = null;

    if (Node.isStringLiteral(eventNameArg)) {
      eventName = eventNameArg.getLiteralValue();
    } else if (Node.isTemplateExpression(eventNameArg)) {
      eventName = eventNameArg.getText().replace(/[`'"]/g, "");
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
    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      this.extractAssignmentsFromFunction(handlerArg, assignments);
      this.extractVerificationConditionsFromFunction(handlerArg, preconditions, postconditions);
    }

    // Infer emitter name from the call expression
    const expression = callExpr.getExpression();
    let emitterName = "central-bus";
    if (Node.isPropertyAccessExpression(expression)) {
      const emitterExpr = expression.getExpression();
      if (Node.isIdentifier(emitterExpr)) {
        emitterName = emitterExpr.getText();
      }
    }

    const sourceFile = callExpr.getSourceFile();
    const line = callExpr.getStartLineNumber();

    return {
      messageType: eventName,
      node: emitterName,
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
