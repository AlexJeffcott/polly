// ═══════════════════════════════════════════════════════════════
// WebSocket Adapter
// ═══════════════════════════════════════════════════════════════
//
// Extracts verification model from Bun WebSocket applications.
// Recognizes:
// - WebSocket server/client communication
// - Eden type definitions for messages
// - Handler functions (handle* pattern)
// - State mutations via global state object
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

export interface WebSocketAdapterConfig extends AdapterConfig {
  /** Whether to use Eden types for message extraction */
  useEdenTypes?: boolean;

  /** Pattern to match handler functions (default: /^handle[A-Z]/) */
  handlerPattern?: RegExp;

  /** Maximum concurrent connections to model (default: 10) */
  maxConnections?: number;

  /** Maximum messages in flight (default: 5) */
  maxInFlight?: number;
}

// ─────────────────────────────────────────────────────────────────
// WebSocket Adapter Implementation
// ─────────────────────────────────────────────────────────────────

export class WebSocketAdapter implements RoutingAdapter<WebSocketAdapterConfig> {
  readonly name = "websocket";
  readonly config: WebSocketAdapterConfig;
  private project: Project;

  constructor(config: WebSocketAdapterConfig) {
    this.config = {
      useEdenTypes: true,
      handlerPattern: /^handle[A-Z]/,
      maxConnections: 10,
      maxInFlight: 5,
      ...config,
    };

    this.project = new Project({
      tsConfigFilePath: config.tsConfigPath,
    });
  }

  /**
   * Extract the complete verification model from the WebSocket application
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

    // Define nodes (server + clients)
    const nodes: NodeDefinition[] = [
      {
        id: "server",
        type: "websocket-server",
        canSendTo: ["*"], // Server can send to all clients
        canReceiveFrom: ["*"], // Server receives from all clients
        metadata: {
          isHub: true,
        },
      },
    ];

    // Add client nodes (bounded for model checking)
    for (let i = 1; i <= this.config.maxConnections!; i++) {
      nodes.push({
        id: `client-${i}`,
        type: "websocket-client",
        canSendTo: ["server"], // Clients send to server
        canReceiveFrom: ["server"], // Clients receive from server
        metadata: {
          clientId: i,
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
        from:
          name.startsWith("USER_") ||
          name.startsWith("CHAT_") ||
          name.startsWith("TODO_") ||
          name.startsWith("SYNC_")
            ? ["client-*"] // Client messages
            : ["server"], // Server messages
        to:
          name.startsWith("USER_") ||
          name.startsWith("CHAT_") ||
          name.startsWith("TODO_") ||
          name.startsWith("SYNC_")
            ? ["server"] // To server
            : ["client-*"], // To clients
      },
    }));

    // Define routing rules (hub-and-spoke pattern)
    const routingRules: RoutingRule[] = [
      {
        pattern: "request-reply",
        messageTypes: Array.from(messageTypeNames),
        description:
          "WebSocket hub-and-spoke: clients send to server, server broadcasts to clients",
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
          maxConnections: this.config.maxConnections!,
        },
      },
    };
  }

  /**
   * Recognize message handler: handle* functions
   */
  recognizeMessageHandler(node: Node): MessageHandler | null {
    if (!Node.isFunctionDeclaration(node)) {
      return null;
    }

    const name = node.getName();
    if (!name || !this.config.handlerPattern!.test(name)) {
      return null;
    }

    return this.extractHandlerFromFunction(node);
  }

  /**
   * Recognize state mutation: state.field = value
   */
  recognizeStateUpdate(node: Node): StateAssignment | null {
    if (!Node.isBinaryExpression(node)) {
      return null;
    }

    const operator = node.getOperatorToken().getText();
    if (operator !== "=" && operator !== "+=" && operator !== "-=") {
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

    // For += and -= operators, we can't extract the exact value
    if (operator !== "=") {
      return null;
    }

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
      // Try to recognize as a function declaration (handle* pattern)
      const handler = this.recognizeMessageHandler(node);
      if (handler) {
        handlers.push(handler);
        return;
      }

      // Try to recognize as an .on() event listener
      const eventHandler = this.recognizeEventListenerHandler(node);
      if (eventHandler) {
        handlers.push(eventHandler);
      }
    });

    return handlers;
  }

  /**
   * Recognize .on() event listener pattern:
   * - wss.on('connection', (ws) => { ... })
   * - ws.on('message', (data) => { ... })
   * - socket.on('chat-message', (msg) => { ... })
   * - io.on('connection', (socket) => { ... })
   */
  private recognizeEventListenerHandler(node: Node): MessageHandler | null {
    if (!Node.isCallExpression(node)) {
      return null;
    }

    const expression = node.getExpression();

    // Check if it's a .on() call
    if (!Node.isPropertyAccessExpression(expression)) {
      return null;
    }

    const methodName = expression.getName();
    if (methodName !== "on") {
      return null;
    }

    const args = node.getArguments();
    if (args.length < 2) {
      return null;
    }

    // First argument should be the event name (string literal)
    const eventNameArg = args[0];
    if (!Node.isStringLiteral(eventNameArg)) {
      return null;
    }

    const messageType = eventNameArg.getLiteralValue();

    // Second argument should be the handler function (arrow function or function expression)
    const handlerArg = args[1];
    if (!Node.isArrowFunction(handlerArg) && !Node.isFunctionExpression(handlerArg)) {
      return null;
    }

    // Extract state mutations and conditions from the handler
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    this.extractAssignmentsFromFunction(handlerArg, assignments);
    this.extractVerificationConditionsFromFunction(handlerArg, preconditions, postconditions);

    const sourceFile = node.getSourceFile();
    const line = node.getStartLineNumber();

    return {
      messageType,
      node: "Server", // WebSocket handlers typically run on server
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
   * Extract handler details from a handle* function
   */
  private extractHandlerFromFunction(funcNode: Node): MessageHandler | null {
    if (!Node.isFunctionDeclaration(funcNode)) {
      return null;
    }

    const name = funcNode.getName();
    if (!name) {
      return null;
    }

    // Extract message type from function name
    // handleUserJoin -> USER_JOIN
    const messageType = this.functionNameToMessageType(name);

    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    // Parse the function body
    this.extractAssignmentsFromFunction(funcNode, assignments);
    this.extractVerificationConditionsFromFunction(funcNode, preconditions, postconditions);

    const sourceFile = funcNode.getSourceFile();
    const line = funcNode.getStartLineNumber();

    return {
      messageType,
      node: "Server", // All handlers run on server
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
   * Convert handler function name to message type
   * handleUserJoin -> USER_JOIN
   */
  private functionNameToMessageType(name: string): string {
    // Remove "handle" prefix
    const withoutHandle = name.replace(/^handle/, "");

    // Convert PascalCase to SCREAMING_SNAKE_CASE
    return withoutHandle
      .replace(/([A-Z])/g, "_$1")
      .replace(/^_/, "")
      .toUpperCase();
  }

  /**
   * Extract state assignments from a function
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
   * Extract verification conditions from a function
   */
  private extractVerificationConditionsFromFunction(
    funcNode: Node,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    // Support function declarations, arrow functions, and function expressions
    if (!Node.isFunctionDeclaration(funcNode) &&
        !Node.isArrowFunction(funcNode) &&
        !Node.isFunctionExpression(funcNode)) {
      return;
    }

    const body = funcNode.getBody();

    if (!body) {
      return;
    }

    // Handle both block statements and expression bodies (arrow functions)
    if (!Node.isBlock(body)) {
      // For arrow functions with expression body, no statements to check
      return;
    }

    // Get all statements in the function body
    const statements = body.getStatements();

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
   * Custom invariants specific to WebSocket systems
   */
  customInvariants(): Array<[name: string, tlaExpression: string]> {
    return [
      [
        "ServerAlwaysAvailable",
        'ports["server"] = "connected"  \\* Server must always be available',
      ],
      [
        "ClientsConnectToServer",
        "\\A msg \\in Range(messages) : " +
          '(msg.source # "server") => ("server" \\in msg.targets)  \\* Clients must route through server',
      ],
      [
        "BroadcastConsistency",
        "\\A c1, c2 \\in Contexts : " +
          '(c1 # "server" /\\ c2 # "server" /\\ ports[c1] = "connected" /\\ ports[c2] = "connected") => ' +
          "\\* All connected clients eventually receive broadcasts",
      ],
    ];
  }
}
