// Type-safe message bus for extension communication

import type { ExtensionAdapters, MessageSender } from "../adapters";
import { createChromeAdapters } from "../adapters";
import type {
  Context,
  ExtensionMessage,
  MessageHandler,
  MessageResponse,
  RoutedMessage,
  RoutedResponse,
} from "../types/messages";
import { ConnectionError, ErrorHandler, HandlerError, TimeoutError } from "./errors";

type PendingRequest = {
  // Accepts the union of all possible response types
  // Type safety is enforced at handler registration (.on) and invocation (send)
  resolve: (value: MessageResponse<ExtensionMessage> | undefined) => void;
  reject: (error: Error) => void;
  timestamp: number;
  timeout: NodeJS.Timeout;
};

export class MessageBus {
  public context: Context;
  public adapters: ExtensionAdapters;
  public pendingRequests = new Map<string, PendingRequest>();
  // Handlers Map stores functions with varying signatures
  // Type safety is enforced at registration (.on()) and invocation (send())
  // biome-ignore lint/complexity/noBannedTypes: Function type needed for dynamic handler map
  private handlers = new Map<string, Function>();
  private port: ReturnType<ExtensionAdapters["runtime"]["connect"]> | null = null;
  private errorHandler: ErrorHandler;
  private messageListener:
    | ((
        message: unknown,
        sender: MessageSender,
        sendResponse: (response: unknown) => void
      ) => boolean)
    | null = null;

  constructor(context: Context, adapters?: ExtensionAdapters) {
    this.context = context;
    this.adapters = adapters || createChromeAdapters(context);
    this.errorHandler = new ErrorHandler(this.adapters.logger);
    this.setupListeners();
  }

  /**
   * Send a message with type safety.
   * Response type is inferred from message type, though TypeScript requires
   * the return type to be widened due to Map storage limitations.
   * Runtime type safety is ensured by handler registration and invocation.
   */
  async send<T extends ExtensionMessage>(
    payload: T,
    options?: {
      target?: Context;
      tabId?: number;
      timeout?: number;
    }
  ): Promise<MessageResponse<ExtensionMessage> | undefined> {
    const id = crypto.randomUUID();
    const target = options?.target || this.inferTarget(payload.type);

    const message: RoutedMessage<T> = {
      id,
      source: this.context,
      target,
      ...(options?.tabId !== undefined && { tabId: options.tabId }),
      timestamp: Date.now(),
      payload,
    };

    return new Promise<MessageResponse<ExtensionMessage> | undefined>((resolve, reject) => {
      const timeoutMs = options?.timeout || 5000;
      const timeout = setTimeout(() => {
        this.pendingRequests.delete(id);
        reject(
          this.errorHandler.reject(
            new TimeoutError(`Message timeout: ${payload.type}`, timeoutMs, {
              messageType: payload.type,
              target,
            })
          )
        );
      }, timeoutMs);

      this.pendingRequests.set(id, {
        resolve: (value) => {
          clearTimeout(timeout);
          resolve(value);
        },
        reject: (error) => {
          clearTimeout(timeout);
          reject(error);
        },
        timestamp: Date.now(),
        timeout,
      });

      // Send via appropriate channel
      this.sendMessage(message);
    });
  }

  /**
   * Broadcast message to all contexts.
   * Used for state synchronization.
   */
  broadcast<T extends ExtensionMessage>(payload: T): void {
    const message: RoutedMessage<T> = {
      id: crypto.randomUUID(),
      source: this.context,
      target: "broadcast",
      timestamp: Date.now(),
      payload,
    };

    this.sendMessage(message);
  }

  /**
   * Register a typed message handler.
   * Handler signature is enforced based on message type.
   */
  on<T extends ExtensionMessage["type"]>(
    type: T,
    handler: (
      payload: Extract<ExtensionMessage, { type: T }>,
      message: RoutedMessage<Extract<ExtensionMessage, { type: T }>>
    ) =>
      | Promise<MessageResponse<Extract<ExtensionMessage, { type: T }>>>
      | MessageResponse<Extract<ExtensionMessage, { type: T }>>
  ): void {
    // Store handler with runtime type safety
    // TypeScript can't verify cross-boundary type safety through the Map storage,
    // but the .on() signature ensures the handler matches the message type
    this.handlers.set(type, handler);
  }

  /**
   * Connect with long-lived port.
   * Used for persistent connections (DevTools, Content Scripts).
   */
  connect(name: string): void {
    if (this.port) {
      console.warn(`[${this.context}] Port already connected: ${this.port.name}`);
      return;
    }

    this.port = this.adapters.runtime.connect(name);

    this.port.onMessage((message: unknown) => {
      this.handleMessage(message as RoutedMessage | RoutedResponse);
    });

    this.port.onDisconnect(() => {
      this.adapters.logger.warn("Port disconnected", {
        context: this.context,
        portName: name,
      });
      this.port = null;

      // Reject all pending requests
      for (const [id, pending] of this.pendingRequests.entries()) {
        pending.reject(
          this.errorHandler.reject(
            new ConnectionError("Port disconnected", {
              context: this.context,
              portName: name,
              requestId: id,
            })
          )
        );
        clearTimeout(pending.timeout);
        this.pendingRequests.delete(id);
      }
    });
  }

  /**
   * Disconnect port if connected.
   */
  disconnect(): void {
    if (this.port) {
      this.port.disconnect();
      this.port = null;
    }
  }

  /**
   * Remove all handlers and clean up.
   */
  destroy(): void {
    this.disconnect();
    this.handlers.clear();

    // Clear all pending requests
    for (const pending of this.pendingRequests.values()) {
      clearTimeout(pending.timeout);
    }
    this.pendingRequests.clear();
  }

  private setupListeners(): void {
    // Listen for one-off messages via chrome.runtime.sendMessage
    this.messageListener = (
      message: unknown,
      sender: unknown,
      sendResponse: (response: unknown) => void
    ) => {
      this.handleMessage(message as RoutedMessage | RoutedResponse, sender)
        .then((response) => sendResponse(response))
        .catch((error) => {
          sendResponse({ success: false, error: error.message });
        });
      return true; // Indicates async response
    };
    this.adapters.runtime.onMessage(this.messageListener);

    // Content/Page script window messaging
    if (this.context === "content" || this.context === "page") {
      this.adapters.window.addEventListener("message", (event: MessageEvent) => {
        if (event.source !== window) return;
        if (event.data?.__extensionMessage) {
          this.handleMessage(event.data.message);
        }
      });
    }
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Message handling requires routing logic for different message types
  public async handleMessage(
    message: RoutedMessage | RoutedResponse,
    _sender?: unknown
  ): Promise<unknown> {
    // Handle response to our request
    if ("success" in message) {
      const pending = this.pendingRequests.get(message.id);
      if (pending) {
        this.pendingRequests.delete(message.id);
        clearTimeout(pending.timeout);

        if (message.success) {
          pending.resolve(message.data ?? undefined);
        } else {
          pending.reject(
            this.errorHandler.reject(
              new HandlerError(message.error || "Unknown error", "unknown", {
                messageId: message.id,
              })
            )
          );
        }
      }
      return;
    }

    // Ignore messages not targeted at us (unless broadcast)
    if (message.target !== this.context && message.target !== "broadcast") {
      // If we're background, we need to route it
      if (this.context === "background") {
        return; // Routing handled elsewhere
      }
      return;
    }

    // Handle incoming request
    const handler = this.handlers.get(message.payload.type);
    if (!handler) {
      if (message.target !== "broadcast") {
        console.warn(`[${this.context}] No handler for message type: ${message.payload.type}`);
      }
      return { success: false, error: "No handler" };
    }

    try {
      const data = await handler(message.payload, message);

      const response: RoutedResponse = {
        id: message.id,
        success: true,
        data,
        timestamp: Date.now(),
      };

      // Send response back (only if not broadcast)
      if (message.target !== "broadcast") {
        this.sendResponse(message, response);
      }

      return response;
    } catch (error) {
      const response: RoutedResponse = {
        id: message.id,
        success: false,
        error: error instanceof Error ? error.message : "Unknown error",
        timestamp: Date.now(),
      };

      if (message.target !== "broadcast") {
        this.sendResponse(message, response);
      }

      return response;
    }
  }

  public sendMessage(message: RoutedMessage): void {
    if (this.context === "content" && message.target === "page") {
      // Content → Page via window.postMessage
      this.adapters.window.postMessage({ __extensionMessage: true, message }, "*");
    } else if (this.context === "page") {
      // Page → Content via window.postMessage
      this.adapters.window.postMessage({ __extensionMessage: true, message }, "*");
    } else if (this.port && (this.context === "devtools" || this.context === "content")) {
      // Use long-lived port if connected
      this.port.postMessage(message);
    } else {
      // Use chrome.runtime.sendMessage
      this.adapters.runtime.sendMessage(message);
    }
  }

  private sendResponse(request: RoutedMessage, response: RoutedResponse): void {
    if (this.context === "content" && request.source === "page") {
      // Content → Page response
      this.adapters.window.postMessage({ __extensionMessage: true, message: response }, "*");
    } else if (this.context === "page" && request.source === "content") {
      // Page → Content response
      this.adapters.window.postMessage({ __extensionMessage: true, message: response }, "*");
    } else if (this.port && (this.context === "devtools" || this.context === "content")) {
      // Use port for response
      this.port.postMessage(response);
    } else {
      // Use chrome.runtime.sendMessage
      this.adapters.runtime.sendMessage(response);
    }
  }

  private inferTarget(type: ExtensionMessage["type"]): Context | "broadcast" {
    const handlers: Partial<MessageHandler> = {
      DOM_QUERY: "content",
      DOM_UPDATE: "content",
      DOM_INSERT: "content",
      DOM_REMOVE: "content",
      PAGE_EVAL: "page",
      PAGE_GET_VAR: "page",
      PAGE_CALL_FN: "page",
      PAGE_SET_VAR: "page",
      API_REQUEST: "background",
      API_BATCH: "background",
      CLIPBOARD_WRITE: "offscreen",
      CLIPBOARD_WRITE_HTML: "offscreen",
      CLIPBOARD_WRITE_RICH: "offscreen",
      CLIPBOARD_READ: "offscreen",
      CONTEXT_MENU_CREATE: "background",
      CONTEXT_MENU_REMOVE: "background",
      TAB_QUERY: "background",
      TAB_GET_CURRENT: "background",
      TAB_RELOAD: "background",
    };

    return handlers[type as keyof MessageHandler] || "background";
  }
}

// Singleton instances per context
const messageBusInstances = new Map<Context, MessageBus>();

export function getMessageBus(context: Context, adapters?: ExtensionAdapters): MessageBus {
  if (!messageBusInstances.has(context)) {
    messageBusInstances.set(context, new MessageBus(context, adapters));
  }
  const bus = messageBusInstances.get(context);
  if (!bus) {
    throw new Error(`Failed to get or create MessageBus for context: ${context}`);
  }
  return bus;
}

export function destroyMessageBus(context: Context): void {
  const bus = messageBusInstances.get(context);
  if (bus) {
    bus.destroy();
    messageBusInstances.delete(context);
  }
}
