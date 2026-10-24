// Message flow analysis - trace messages between contexts

import type { CallExpression, Node } from "typescript-7/ast";
import {
  isCallExpression,
  isIdentifier,
  isObjectLiteralExpression,
  isPropertyAccessExpression,
  isPropertyAssignment,
  isStringLiteral,
} from "typescript-7/ast/is";
import {
  type AnalysisProgram,
  type AnalysisSource,
  forEachDescendant,
  jsDocs,
  jsDocText,
  nameOf,
  objectProperty,
  startLine,
  textOf,
  withProgram,
} from "../program";
import type { MessageFlow, MessageStep } from "../types/architecture";
import type { MessageHandler } from "../types/core";

export class FlowAnalyzer {
  private tsConfigPath: string;
  private handlers: MessageHandler[];
  private contextOverrides: Map<string, string>;

  constructor(
    tsConfigPath: string,
    handlers: MessageHandler[],
    contextOverrides?: Map<string, string>
  ) {
    this.tsConfigPath = tsConfigPath;
    this.handlers = handlers;
    this.contextOverrides = contextOverrides || new Map();
  }

  /**
   * Analyze message flows between contexts. With no `source`, opens (and
   * closes) a session of its own; a passed source stays the caller's.
   */
  analyzeFlows(source?: AnalysisSource): Promise<MessageFlow[]> {
    return withProgram(this.tsConfigPath, source, (program) => this.flowsIn(program));
  }

  private flowsIn(program: AnalysisProgram): MessageFlow[] {
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
      const senders = this.findMessageSenders(program, messageType);

      // For each sender, create a flow
      for (const sender of senders) {
        const recipients = handlers.map((h) => h.node);

        // Build sequence of steps
        const sequence = this.buildSequence(program, messageType, sender, handlers);

        // Extract flow metadata
        const flowMetadata = this.extractFlowMetadata(program, sender.file, sender.line);

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
  private findMessageSenders(
    program: AnalysisProgram,
    messageType: string
  ): Array<{
    context: string;
    file: string;
    line: number;
  }> {
    const senders: Array<{ context: string; file: string; line: number }> = [];

    for (const sourceFile of program.sourceFiles) {
      const filePath = sourceFile.fileName;
      const context = this.inferContext(filePath);

      forEachDescendant(sourceFile, (node) => {
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
    if (!isCallExpression(node)) {
      return;
    }

    const expression = node.expression;

    if (isPropertyAccessExpression(expression)) {
      this.processPropertyAccessSender(node, expression, messageType, context, filePath, senders);
    } else if (isIdentifier(expression)) {
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
    if (!isPropertyAccessExpression(expression)) {
      return;
    }

    const methodName = nameOf(expression) ?? "";

    if (!this.isMessageSendMethod(methodName)) {
      return;
    }

    const args = node.arguments;
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
        line: startLine(node),
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
    if (!isIdentifier(expression)) {
      return;
    }

    if (textOf(expression) !== "postMessage") {
      return;
    }

    const args = node.arguments;
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
        line: startLine(node),
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
    program: AnalysisProgram,
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
      const subsends = this.findMessagesInHandler(program, handler);
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
  private findMessagesInHandler(
    program: AnalysisProgram,
    handler: MessageHandler
  ): Array<{
    messageType: string;
    location: { file: string; line: number };
  }> {
    const sends: Array<{ messageType: string; location: { file: string; line: number } }> = [];

    const sourceFile = program.sourceFile(handler.location.file);
    if (!sourceFile) return sends;

    const targetLine = handler.location.line;

    forEachDescendant(sourceFile, (node) => {
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
    if (!isCallExpression(node)) {
      return;
    }

    const line = startLine(node);
    if (!this.isNearLine(line, targetLine)) {
      return;
    }

    const expression = node.expression;
    if (!this.isSendOrEmitCall(expression)) {
      return;
    }

    const args = node.arguments;
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
    if (!isPropertyAccessExpression(expression)) {
      return false;
    }

    const methodName = nameOf(expression);
    return methodName === "send" || methodName === "emit";
  }

  /**
   * Extract message type from send/emit argument
   */
  private extractMessageTypeFromArg(arg: Node): string | undefined {
    if (isStringLiteral(arg)) {
      return arg.text;
    }

    if (isObjectLiteralExpression(arg)) {
      return this.extractMessageTypeFromObject(arg);
    }

    return undefined;
  }

  /**
   * Extract message type from object literal
   */
  private extractMessageTypeFromObject(obj: Node): string | undefined {
    if (!isObjectLiteralExpression(obj)) {
      return undefined;
    }

    const typeProperty = objectProperty(obj, "type");
    if (!typeProperty || !isPropertyAssignment(typeProperty)) {
      return undefined;
    }

    const initializer = typeProperty.initializer;
    if (!isStringLiteral(initializer)) {
      return undefined;
    }

    return initializer.text;
  }

  /**
   * Extract flow metadata from JSDoc annotations
   */
  private extractFlowMetadata(
    program: AnalysisProgram,
    filePath: string,
    lineNumber: number
  ): {
    trigger?: string;
    flowName?: string;
    description?: string;
  } {
    const sourceFile = program.sourceFile(filePath);
    if (!sourceFile) return {};

    // Find the node at this line (the last one in traversal order)
    const atLine: Node[] = [];
    forEachDescendant(sourceFile, (node) => {
      if (startLine(node, sourceFile) === lineNumber) {
        atLine.push(node);
      }
    });
    const targetNode = atLine.at(-1);

    // Only a JSDoc-able node carries the annotations
    const firstDoc = jsDocs(targetNode)[0];
    if (!firstDoc) return {};

    const comment = jsDocText(firstDoc, sourceFile);

    // Extract @flow annotation
    const flowName = comment.match(/@flow\s+([^\s]+)/)?.[1];

    // Extract @trigger annotation
    const trigger = comment.match(/@trigger\s+(.+?)(?:\n|$)/)?.[1]?.trim();

    // Extract @description
    const description = comment.match(/@description\s+(.+?)(?:\n|$)/s)?.[1]?.trim();

    return { trigger, flowName, description };
  }

  /**
   * Infer context from file path
   */
  private inferContext(filePath: string): string {
    // Check context overrides first (monorepo workspace packages)
    for (const [pathPrefix, context] of this.contextOverrides.entries()) {
      if (filePath.startsWith(pathPrefix)) return context;
    }

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
