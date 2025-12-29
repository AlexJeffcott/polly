// Message flow analysis - trace messages between contexts

import { Node, Project } from "ts-morph";
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
        if (Node.isCallExpression(node)) {
          const expression = node.getExpression();

          // Pattern 1: .send() or .emit() calls (ws.send, socket.emit, bus.send, etc.)
          if (Node.isPropertyAccessExpression(expression)) {
            const methodName = expression.getName();

            if (
              methodName === "send" ||
              methodName === "emit" ||
              methodName === "postMessage" ||
              methodName === "broadcast"
            ) {
              const args = node.getArguments();
              if (args.length > 0) {
                const firstArg = args[0];

                let msgType: string | undefined;

                // Check if first argument is a string literal: send("MESSAGE")
                if (Node.isStringLiteral(firstArg)) {
                  msgType = firstArg.getLiteralValue();
                }
                // Check if first argument is an object literal: send({ type: "MESSAGE" })
                else if (Node.isObjectLiteralExpression(firstArg)) {
                  const typeProperty = firstArg.getProperty("type");
                  if (typeProperty && Node.isPropertyAssignment(typeProperty)) {
                    const initializer = typeProperty.getInitializer();
                    if (initializer && Node.isStringLiteral(initializer)) {
                      msgType = initializer.getLiteralValue();
                    }
                  }
                }

                if (msgType === messageType) {
                  senders.push({
                    context,
                    file: filePath,
                    line: node.getStartLineNumber(),
                  });
                }
              }
            }
          }

          // Pattern 2: Standalone postMessage() calls (Web Workers, Window.postMessage)
          if (Node.isIdentifier(expression)) {
            if (expression.getText() === "postMessage") {
              const args = node.getArguments();
              if (args.length > 0) {
                const firstArg = args[0];
                let msgType: string | undefined;

                if (Node.isStringLiteral(firstArg)) {
                  msgType = firstArg.getLiteralValue();
                } else if (Node.isObjectLiteralExpression(firstArg)) {
                  const typeProperty = firstArg.getProperty("type");
                  if (typeProperty && Node.isPropertyAssignment(typeProperty)) {
                    const initializer = typeProperty.getInitializer();
                    if (initializer && Node.isStringLiteral(initializer)) {
                      msgType = initializer.getLiteralValue();
                    }
                  }
                }

                if (msgType === messageType) {
                  senders.push({
                    context,
                    file: filePath,
                    line: node.getStartLineNumber(),
                  });
                }
              }
            }
          }
        }
      });
    }

    return senders;
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

    // Find the handler function at the given line
    const targetLine = handler.location.line;

    sourceFile.forEachDescendant((node) => {
      if (Node.isCallExpression(node)) {
        const line = node.getStartLineNumber();

        // Rough heuristic: if it's near the handler line, it's probably in the handler
        if (Math.abs(line - targetLine) < 20) {
          const expression = node.getExpression();

          if (Node.isPropertyAccessExpression(expression)) {
            const methodName = expression.getName();

            if (methodName === "send" || methodName === "emit") {
              const args = node.getArguments();
              if (args.length > 0) {
                const firstArg = args[0];
                let messageType: string | undefined;

                // Check if first argument is a string literal: send("MESSAGE")
                if (Node.isStringLiteral(firstArg)) {
                  messageType = firstArg.getLiteralValue();
                }
                // Check if first argument is an object literal: send({ type: "MESSAGE" })
                else if (Node.isObjectLiteralExpression(firstArg)) {
                  const typeProperty = firstArg.getProperty("type");
                  if (typeProperty && Node.isPropertyAssignment(typeProperty)) {
                    const initializer = typeProperty.getInitializer();
                    if (initializer && Node.isStringLiteral(initializer)) {
                      messageType = initializer.getLiteralValue();
                    }
                  }
                }

                if (messageType) {
                  sends.push({
                    messageType,
                    location: {
                      file: handler.location.file,
                      line,
                    },
                  });
                }
              }
            }
          }
        }
      }
    });

    return sends;
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
    let targetNode: any = null;

    sourceFile.forEachDescendant((node) => {
      if (node.getStartLineNumber() === lineNumber) {
        targetNode = node;
      }
    });

    if (!targetNode) return {};

    // Look for JSDoc comments
    const jsDocs = targetNode.getJsDocs?.() || [];
    if (jsDocs.length === 0) return {};

    const comment = jsDocs[0].getText();

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

    // WebSocket/server app contexts
    if (path.includes("/server/") || path.includes("\\server\\") || path.includes("/server.")) {
      return "server";
    }
    if (path.includes("/client/") || path.includes("\\client\\") || path.includes("/client.")) {
      return "client";
    }

    // PWA/Worker contexts
    if (
      path.includes("/worker/") ||
      path.includes("\\worker\\") ||
      path.includes("service-worker")
    ) {
      return "worker";
    }

    return "unknown";
  }
}
