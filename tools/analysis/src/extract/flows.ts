// Message flow analysis - trace messages between contexts

import { type CallExpression, Node, Project } from "ts-morph";
import type { MessageFlow, MessageStep } from "../types/architecture";
import type { MessageHandler } from "../types/core";

export class FlowAnalyzer {
  private project: Project;
  private handlers: MessageHandler[];

  constructor(tsConfigPath: string, handlers: MessageHandler[]) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
    this.handlers = handlers;
  }

  /**
   * Analyze message flows between contexts
   */
  analyzeFlows(): MessageFlow[] {
    const flows: MessageFlow[] = [];

    // Group handlers by message type
    const handlersByType = new Map<string, MessageHandler[]>();
    for (const handler of this.handlers) {
      if (!handlersByType.has(handler.messageType)) {
        handlersByType.set(handler.messageType, []);
      }
      handlersByType.get(handler.messageType)?.push(handler);
    }

    // For each message type, trace the flow
    for (const [messageType, handlers] of handlersByType) {
      // Find senders
      const senders = this.findMessageSenders(messageType);

      // For each sender, create a flow
      for (const sender of senders) {
        const recipients = handlers.map((h) => h.node);

        // Build sequence of steps
        const sequence = this.buildSequence(messageType, sender, handlers);

        // Extract flow metadata
        const flowMetadata = this.extractFlowMetadata(sender.file, sender.line);

        flows.push({
          messageType,
          from: sender.context,
          to: recipients,
          ...(flowMetadata.trigger ? { trigger: flowMetadata.trigger } : {}),
          ...(flowMetadata.flowName ? { flowName: flowMetadata.flowName } : {}),
          ...(flowMetadata.description ? { description: flowMetadata.description } : {}),
          sequence,
        });
      }
    }

    return flows;
  }

  /**
   * Find all places where a message is sent
   * Supports: .send(), .emit(), postMessage(), ws.send(), broadcast(), etc.
   */
  private findMessageSenders(messageType: string): Array<{
    context: string;
    file: string;
    line: number;
  }> {
    const senders: Array<{ context: string; file: string; line: number }> = [];

    for (const sourceFile of this.project.getSourceFiles()) {
      const filePath = sourceFile.getFilePath();
      const context = this.inferContext(filePath);

      sourceFile.forEachDescendant((node) => {
        this.processMessageSender(node, messageType, context, filePath, senders);
      });
    }

    return senders;
  }

  /**
   * Process a node that might be a message sender
   */
  private processMessageSender(
    node: Node,
    messageType: string,
    context: string,
    filePath: string,
    senders: Array<{ context: string; file: string; line: number }>
  ): void {
    if (!Node.isCallExpression(node)) {
      return;
    }

    const expression = node.getExpression();

    if (Node.isPropertyAccessExpression(expression)) {
      this.processPropertyAccessSender(node, expression, messageType, context, filePath, senders);
    } else if (Node.isIdentifier(expression)) {
      this.processIdentifierSender(node, expression, messageType, context, filePath, senders);
    }
  }

  /**
   * Process property access sender (.send(), .emit(), etc.)
   */
  private processPropertyAccessSender(
    node: CallExpression,
    expression: Node,
    messageType: string,
    context: string,
    filePath: string,
    senders: Array<{ context: string; file: string; line: number }>
  ): void {
    if (!Node.isPropertyAccessExpression(expression)) {
      return;
    }

    const methodName = expression.getName();

    if (!this.isMessageSendMethod(methodName)) {
      return;
    }

    const args = node.getArguments();
    if (args.length === 0) {
      return;
    }

    const firstArg = args[0];
    if (!firstArg) return;

    const msgType = this.extractMessageTypeFromArg(firstArg);
    if (msgType === messageType) {
      senders.push({
        context,
        file: filePath,
        line: node.getStartLineNumber(),
      });
    }
  }

  /**
   * Process identifier sender (postMessage())
   */
  private processIdentifierSender(
    node: CallExpression,
    expression: Node,
    messageType: string,
    context: string,
    filePath: string,
    senders: Array<{ context: string; file: string; line: number }>
  ): void {
    if (!Node.isIdentifier(expression)) {
      return;
    }

    if (expression.getText() !== "postMessage") {
      return;
    }

    const args = node.getArguments();
    if (args.length === 0) {
      return;
    }

    const firstArg = args[0];
    if (!firstArg) return;

    const msgType = this.extractMessageTypeFromArg(firstArg);
    if (msgType === messageType) {
      senders.push({
        context,
        file: filePath,
        line: node.getStartLineNumber(),
      });
    }
  }

  /**
   * Check if method name is a message sending method
   */
  private isMessageSendMethod(methodName: string): boolean {
    return (
      methodName === "send" ||
      methodName === "emit" ||
      methodName === "postMessage" ||
      methodName === "broadcast"
    );
  }

  /**
   * Build sequence of steps for a message flow
   */
  private buildSequence(
    messageType: string,
    sender: { context: string; file: string; line: number },
    handlers: MessageHandler[]
  ): MessageStep[] {
    const steps: MessageStep[] = [];
    let stepNumber = 1;

    // Step 1: Send message
    steps.push({
      step: stepNumber++,
      action: `${sender.context}.send(${messageType})`,
      context: sender.context,
      location: {
        file: sender.file,
        line: sender.line,
      },
    });

    // Step 2+: Handle in each recipient context
    for (const handler of handlers) {
      steps.push({
        step: stepNumber++,
        action: `${handler.node}.handle(${messageType})`,
        context: handler.node,
        location: handler.location,
      });

      // Add substeps for any messages sent by this handler
      const subsends = this.findMessagesInHandler(handler);
      for (const subsend of subsends) {
        steps.push({
          step: stepNumber++,
          action: `${handler.node}.send(${subsend.messageType})`,
          context: handler.node,
          location: subsend.location,
        });
      }
    }

    return steps;
  }

  /**
   * Find messages sent within a handler
   */
  private findMessagesInHandler(handler: MessageHandler): Array<{
    messageType: string;
    location: { file: string; line: number };
  }> {
    const sends: Array<{ messageType: string; location: { file: string; line: number } }> = [];

    const sourceFile = this.project.getSourceFile(handler.location.file);
    if (!sourceFile) return sends;

    const targetLine = handler.location.line;

    sourceFile.forEachDescendant((node) => {
      this.processSendCall(node, targetLine, handler.location.file, sends);
    });

    return sends;
  }

  /**
   * Process a node that might be a send/emit call
   */
  private processSendCall(
    node: Node,
    targetLine: number,
    filePath: string,
    sends: Array<{ messageType: string; location: { file: string; line: number } }>
  ): void {
    if (!Node.isCallExpression(node)) {
      return;
    }

    const line = node.getStartLineNumber();
    if (!this.isNearLine(line, targetLine)) {
      return;
    }

    const expression = node.getExpression();
    if (!this.isSendOrEmitCall(expression)) {
      return;
    }

    const args = node.getArguments();
    if (args.length === 0) {
      return;
    }

    const firstArg = args[0];
    if (!firstArg) return;

    const messageType = this.extractMessageTypeFromArg(firstArg);
    if (messageType) {
      sends.push({
        messageType,
        location: { file: filePath, line },
      });
    }
  }

  /**
   * Check if line is near target line
   */
  private isNearLine(line: number, targetLine: number): boolean {
    return Math.abs(line - targetLine) < 20;
  }

  /**
   * Check if expression is a send or emit call
   */
  private isSendOrEmitCall(expression: Node): boolean {
    if (!Node.isPropertyAccessExpression(expression)) {
      return false;
    }

    const methodName = expression.getName();
    return methodName === "send" || methodName === "emit";
  }

  /**
   * Extract message type from send/emit argument
   */
  private extractMessageTypeFromArg(arg: Node): string | undefined {
    if (Node.isStringLiteral(arg)) {
      return arg.getLiteralValue();
    }

    if (Node.isObjectLiteralExpression(arg)) {
      return this.extractMessageTypeFromObject(arg);
    }

    return undefined;
  }

  /**
   * Extract message type from object literal
   */
  private extractMessageTypeFromObject(obj: Node): string | undefined {
    if (!Node.isObjectLiteralExpression(obj)) {
      return undefined;
    }

    const typeProperty = obj.getProperty("type");
    if (!typeProperty || !Node.isPropertyAssignment(typeProperty)) {
      return undefined;
    }

    const initializer = typeProperty.getInitializer();
    if (!initializer || !Node.isStringLiteral(initializer)) {
      return undefined;
    }

    return initializer.getLiteralValue();
  }

  /**
   * Extract flow metadata from JSDoc annotations
   */
  private extractFlowMetadata(
    filePath: string,
    lineNumber: number
  ): {
    trigger?: string;
    flowName?: string;
    description?: string;
  } {
    const sourceFile = this.project.getSourceFile(filePath);
    if (!sourceFile) return {};

    // Find the node at this line
    let targetNode: Node | null = null;

    sourceFile.forEachDescendant((node) => {
      if (node.getStartLineNumber() === lineNumber) {
        targetNode = node;
      }
    });

    if (!targetNode) return {};

    // Look for JSDoc comments - use type guard to check if node supports JSDoc
    // biome-ignore lint/suspicious/noExplicitAny: Type guard for dynamic JSDoc support
    const nodeAny = targetNode as any;
    if (!("getJsDocs" in nodeAny) || typeof nodeAny.getJsDocs !== "function") {
      return {};
    }

    const jsDocs = nodeAny.getJsDocs();
    if (jsDocs.length === 0) return {};

    const firstDoc = jsDocs[0];
    if (!firstDoc) return {};

    const comment = firstDoc.getText();

    // Extract @flow annotation
    const flowMatch = comment.match(/@flow\s+([^\s]+)/);
    const flowName = flowMatch ? flowMatch[1] : undefined;

    // Extract @trigger annotation
    const triggerMatch = comment.match(/@trigger\s+(.+?)(?:\n|$)/);
    const trigger = triggerMatch ? triggerMatch[1].trim() : undefined;

    // Extract @description
    const descMatch = comment.match(/@description\s+(.+?)(?:\n|$)/s);
    const description = descMatch ? descMatch[1].trim() : undefined;

    return { trigger, flowName, description };
  }

  /**
   * Infer context from file path
   */
  private inferContext(filePath: string): string {
    const path = filePath.toLowerCase();

    // Define context patterns to check
    const contextPatterns: Array<{ context: string; patterns: string[] }> = [
      { context: "background", patterns: ["/background/", "\\background\\"] },
      { context: "content", patterns: ["/content/", "\\content\\"] },
      { context: "popup", patterns: ["/popup/", "\\popup\\"] },
      { context: "devtools", patterns: ["/devtools/", "\\devtools\\"] },
      { context: "options", patterns: ["/options/", "\\options\\"] },
      { context: "offscreen", patterns: ["/offscreen/", "\\offscreen\\"] },
      { context: "server", patterns: ["/server/", "\\server\\", "/server."] },
      { context: "client", patterns: ["/client/", "\\client\\", "/client."] },
      { context: "worker", patterns: ["/worker/", "\\worker\\", "service-worker"] },
    ];

    for (const { context, patterns } of contextPatterns) {
      if (patterns.some((pattern) => path.includes(pattern))) {
        return context;
      }
    }

    return "unknown";
  }
}
