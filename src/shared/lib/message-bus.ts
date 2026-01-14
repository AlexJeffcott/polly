// Type-safe message bus for extension communication

import type { ExtensionAdapters, MessageSender } from "../adapters";
import { createChromeAdapters } from "../adapters";
import type {
  BaseMessage,
  Context,
  ExtensionMessage,
  MessageResponse,
  RoutedMessage,
  RoutedResponse,
} from "../types/messages";
import { ALL_CONTEXTS } from "../types/messages";
import type {
  BackgroundHelpers,
  ContentScriptHelpers,
  DevToolsHelpers,
  OptionsHelpers,
  PopupHelpers,
  SidePanelHelpers,
} from "./context-specific-helpers";
import {
  createBackgroundHelpers,
  createContentScriptHelpers,
  createDevToolsHelpers,
  createOptionsHelpers,
  createPopupHelpers,
  createSidePanelHelpers,
} from "./context-specific-helpers";
import { ConnectionError, ErrorHandler, HandlerError, TimeoutError } from "./errors";
import { globalExecutionTracker } from "./handler-execution-tracker";

// Type guards for runtime message validation
// Note: These validate structure but can't validate TMessage type at runtime
export function isRoutedMessage<TMessage extends BaseMessage = BaseMessage>(
  value: unknown
): value is RoutedMessage<TMessage> {
  if (typeof value !== "object" || value === null) return false;
  // Use 'in' operator for type narrowing - no cast needed
  if (!("id" in value) || !("source" in value) || !("targets" in value) || !("payload" in value)) {
    return false;
  }
  // TypeScript now knows these properties exist
  return (
    typeof value.id === "string" &&
    typeof value.source === "string" &&
    Array.isArray(value.targets) &&
    typeof value.payload === "object" &&
    value.payload !== null
  );
}

export function isRoutedResponse<TMessage extends BaseMessage = BaseMessage>(
  value: unknown
): value is RoutedResponse<TMessage> {
  if (typeof value !== "object" || value === null) return false;
  // Use 'in' operator for type narrowing - no cast needed
  if (!("id" in value) || !("success" in value)) {
    return false;
  }
  // TypeScript now knows these properties exist
  return typeof value.id === "string" && typeof value.success === "boolean";
}

type PendingRequest<TMessage extends BaseMessage = ExtensionMessage> = {
  // Accepts the union of all possible response types
  // Type safety is enforced at handler registration (.on) and invocation (send)
  resolve: (value: MessageResponse<TMessage> | undefined) => void;
  reject: (error: Error) => void;
  timestamp: number;
  timeout: NodeJS.Timeout;
};

export class MessageBus<TMessage extends BaseMessage = ExtensionMessage> {
  public context: Context;
  public adapters: ExtensionAdapters;
  public helpers:
    | ContentScriptHelpers
    | DevToolsHelpers
    | PopupHelpers
    | OptionsHelpers
    | SidePanelHelpers
    | BackgroundHelpers
    | Record<string, never>;
  public pendingRequests = new Map<string, PendingRequest<TMessage>>();
  // Handlers Map stores arrays of functions with varying signatures
  // Type safety is enforced at registration (.on()) and invocation (send())
  // biome-ignore lint/complexity/noBannedTypes: Function type needed for dynamic handler map
  private handlers = new Map<string, Function[]>();
  private port: ReturnType<ExtensionAdapters["runtime"]["connect"]> | null = null;
  private errorHandler: ErrorHandler;
  private userErrorHandlers: Array<(error: Error, bus: MessageBus<TMessage>) => void> = [];
  private stateAccessor: (() => unknown) | null = null;
  public messageListener:
    | ((
        message: unknown,
        sender: MessageSender,
        sendResponse: (response: unknown) => void
      ) => boolean)
    | null = null;

  constructor(
    context: Context,
    adapters?: ExtensionAdapters,
    options?: { skipListenerSetup?: boolean }
  ) {
    this.context = context;
    this.adapters = adapters || createChromeAdapters(context);
    this.errorHandler = new ErrorHandler(this.adapters.logger);
    this.helpers = this.createContextHelpers();

    // Skip listener setup if MessageRouter will handle it
    if (!options?.skipListenerSetup) {
      this.setupListeners();
    }
  }

  /**
   * Send a message with type safety.
   * Response type is inferred from message type, though TypeScript requires
   * the return type to be widened due to Map storage limitations.
   * Runtime type safety is ensured by handler registration and invocation.
   */
  async send<T extends TMessage>(
    payload: T,
    options?: {
      target?: Context | Context[];
      tabId?: number;
      timeout?: number;
    }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    const id = crypto.randomUUID();

    // For custom messages (not ExtensionMessage), targets must be explicitly provided
    let targets: Context[];
    if (options?.target) {
      // Handle single target from options
      if (Array.isArray(options.target)) {
        targets = options.target;
      } else {
        targets = [options.target];
      }
    } else {
      const inferredTarget = this.inferTarget(payload.type);
      if (!inferredTarget) {
        throw new Error(
          `Message type "${payload.type}" is not a framework message. Please provide explicit 'target' option.`
        );
      }
      // inferredTarget can be a single context or an array
      targets = Array.isArray(inferredTarget) ? inferredTarget : [inferredTarget];
    }

    const message: RoutedMessage<T> = {
      id,
      source: this.context,
      targets,
      ...(options?.tabId !== undefined && { tabId: options.tabId }),
      timestamp: Date.now(),
      payload,
    };

    return new Promise<MessageResponse<T> | undefined>((resolve, reject) => {
      const timeoutMs = options?.timeout || 5000;
      const timeout = setTimeout(() => {
        this.pendingRequests.delete(id);
        const error = new TimeoutError(`Message timeout: ${payload.type}`, timeoutMs, {
          messageType: payload.type,
          targets,
        });
        this.notifyErrorHandlers(error);
        reject(this.errorHandler.reject(error));
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
  broadcast<T extends TMessage>(payload: T): void {
    const message: RoutedMessage<T> = {
      id: crypto.randomUUID(),
      source: this.context,
      targets: ALL_CONTEXTS,
      timestamp: Date.now(),
      payload,
    };

    this.sendMessage(message);
  }

  /**
   * Register a typed message handler.
   * Handler signature is enforced based on message type.
   * Multiple handlers can be registered for the same message type.
   */
  on<T extends TMessage["type"]>(
    type: T,
    handler: (
      payload: Extract<TMessage, { type: T }>,
      message: RoutedMessage<Extract<TMessage, { type: T }>>
    ) =>
      | Promise<MessageResponse<Extract<TMessage, { type: T }>>>
      | MessageResponse<Extract<TMessage, { type: T }>>
  ): void {
    // Store handler with runtime type safety
    // TypeScript can't verify cross-boundary type safety through the Map storage,
    // but the .on() signature ensures the handler matches the message type
    const existing = this.handlers.get(type) || [];
    existing.push(handler);
    this.handlers.set(type, existing);
  }

  /**
   * Register multiple message handlers at once.
   * Reduces boilerplate when defining many handlers.
   *
   * @example
   * ```typescript
   * bus.registerHandlers({
   *   'MY_MESSAGE': async (payload) => ({ success: true }),
   *   'ANOTHER_MESSAGE': async (payload) => ({ data: payload }),
   * })
   * ```
   */
  // biome-ignore lint/complexity/noBannedTypes: Need to accept user-defined message types beyond ExtensionMessage
  registerHandlers(handlers: Record<string, Function | undefined>): void {
    for (const [type, handler] of Object.entries(handlers)) {
      if (handler) {
        const existing = this.handlers.get(type) || [];
        existing.push(handler);
        this.handlers.set(type, existing);
      }
    }
  }

  /**
   * Register a global error handler.
   * Called when errors occur during message handling.
   *
   * @example
   * ```typescript
   * bus.onError((error, bus) => {
   *   console.error(`[${bus.context}] Error:`, error)
   *   // Report to error tracking service
   * })
   * ```
   */
  onError(handler: (error: Error, bus: MessageBus<TMessage>) => void): void {
    this.userErrorHandlers.push(handler);
  }

  /**
   * Register a state accessor for runtime constraint checking.
   * The accessor function should return the current state object that constraints will check against.
   *
   * @param accessor - Function that returns the current state object
   *
   * @example
   * ```typescript
   * const state = { loggedIn: false };
   * bus.setStateAccessor(() => state);
   *
   * // Now constraints can be checked against this state
   * $constraints("loggedIn", {
   *   USER_LOGOUT: {
   *     requires: (s) => s.loggedIn === true,
   *     message: "Must be logged in"
   *   }
   * }, { runtime: true });
   * ```
   */
  setStateAccessor(accessor: () => unknown): void {
    this.stateAccessor = accessor;
  }

  /**
   * Send message to background context.
   * Explicit routing API for better DX.
   *
   * @example
   * ```typescript
   * const result = await bus.sendToBackground({ type: 'GET_SETTINGS' })
   * ```
   */
  async sendToBackground<T extends TMessage>(
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    return this.send(payload, { ...options, target: "background" });
  }

  /**
   * Send message to a specific content script.
   *
   * @example
   * ```typescript
   * const result = await bus.sendToContentScript(tabId, { type: 'ANALYZE_PAGE' })
   * ```
   */
  async sendToContentScript<T extends TMessage>(
    tabId: number,
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    return this.send(payload, { ...options, target: "content", tabId });
  }

  /**
   * Send message to all tabs.
   * Useful for broadcasting updates to all content scripts.
   *
   * @example
   * ```typescript
   * await bus.sendToAllTabs({ type: 'REFRESH_UI' })
   * ```
   */
  async sendToAllTabs<T extends TMessage>(
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    Array<
      | MessageResponse<
          Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>
        >
      | undefined
    >
  > {
    const tabs = await this.adapters.tabs.query({});
    return Promise.all(
      tabs.map((tab) =>
        tab.id ? this.sendToContentScript(tab.id, payload, options) : Promise.resolve(undefined)
      )
    );
  }

  /**
   * Send message to popup context.
   *
   * @example
   * ```typescript
   * await bus.sendToPopup({ type: 'UPDATE_UI', data: newData })
   * ```
   */
  async sendToPopup<T extends TMessage>(
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    return this.send(payload, { ...options, target: "popup" });
  }

  /**
   * Send message to options page.
   *
   * @example
   * ```typescript
   * await bus.sendToOptions({ type: 'SETTINGS_UPDATED' })
   * ```
   */
  async sendToOptions<T extends TMessage>(
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    return this.send(payload, { ...options, target: "options" });
  }

  /**
   * Send message to devtools panel.
   *
   * @example
   * ```typescript
   * await bus.sendToDevTools({ type: 'INSPECTION_DATA', data: pageData })
   * ```
   */
  async sendToDevTools<T extends TMessage>(
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    return this.send(payload, { ...options, target: "devtools" });
  }

  /**
   * Send message to side panel.
   *
   * @example
   * ```typescript
   * await bus.sendToSidePanel({ type: 'UPDATE_ACTIVITY_LOG' })
   * ```
   */
  async sendToSidePanel<T extends TMessage>(
    payload: T,
    options?: { timeout?: number }
  ): Promise<
    | MessageResponse<Extract<TMessage, { type: T extends { type: infer TType } ? TType : never }>>
    | undefined
  > {
    return this.send(payload, { ...options, target: "sidepanel" });
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
      if (isRoutedMessage<TMessage>(message) || isRoutedResponse<TMessage>(message)) {
        this.handleMessage(message);
      }
    });

    this.port.onDisconnect(() => {
      this.adapters.logger.warn("Port disconnected", {
        context: this.context,
        portName: name,
      });
      this.port = null;

      // Reject all pending requests
      for (const [id, pending] of this.pendingRequests.entries()) {
        const error = new ConnectionError("Port disconnected", {
          context: this.context,
          portName: name,
          requestId: id,
        });
        this.notifyErrorHandlers(error);
        pending.reject(this.errorHandler.reject(error));
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

    // Remove message listener to prevent leaks
    if (this.messageListener) {
      this.adapters.runtime.removeMessageListener(this.messageListener);
    }
  }

  private setupListeners(): void {
    // Listen for one-off messages via chrome.runtime.sendMessage
    this.messageListener = (
      message: unknown,
      sender: unknown,
      sendResponse: (response: unknown) => void
    ) => {
      if (isRoutedMessage<TMessage>(message) || isRoutedResponse<TMessage>(message)) {
        this.handleMessage(message, sender)
          .then((response) => sendResponse(response))
          .catch((error) => {
            sendResponse({ success: false, error: error.message });
          });
      }
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
    message: RoutedMessage<TMessage> | RoutedResponse<TMessage>,
    _sender?: unknown
  ): Promise<unknown> {
    // Handle response to our request
    if ("success" in message) {
      const pending = this.pendingRequests.get(message.id);
      if (pending) {
        this.pendingRequests.delete(message.id);
        clearTimeout(pending.timeout);

        if (message.success) {
          // Message data is typed as MessageResponse<TMessage> from RoutedResponse
          pending.resolve(message.data ?? undefined);
        } else {
          const error = new HandlerError(message.error || "Unknown error", "unknown", {
            messageId: message.id,
          });
          this.notifyErrorHandlers(error);
          pending.reject(this.errorHandler.reject(error));
        }
      }
      return;
    }

    // Ignore messages not targeted at us
    if (!message.targets.includes(this.context)) {
      // If we're background, we need to route it
      if (this.context === "background") {
        return; // Routing handled elsewhere
      }
      return;
    }

    // Handle incoming request
    const handlers = this.handlers.get(message.payload.type);
    if (!handlers || handlers.length === 0) {
      // For multi-target messages, don't warn if we have no handler
      if (message.targets.length === 1) {
        console.warn(`[${this.context}] No handler for message type: ${message.payload.type}`);
      }
      return { success: false, error: "No handler" };
    }

    // For multi-target messages (including broadcasts), call all handlers (don't send responses)
    if (message.targets.length > 1) {
      try {
        // Track execution to detect double-handler invocation
        globalExecutionTracker.track(message.id, message.payload.type);

        await Promise.all(handlers.map((handler) => handler(message.payload, message)));
        return { success: true, data: undefined, timestamp: Date.now() };
      } catch (error) {
        return {
          success: false,
          error: error instanceof Error ? error.message : "Unknown error",
          timestamp: Date.now(),
        };
      }
    }

    // For LOG messages, call all handlers but still send response (for backwards compat)
    if (message.payload.type === "LOG") {
      try {
        // Track execution to detect double-handler invocation
        globalExecutionTracker.track(message.id, message.payload.type);

        await Promise.all(handlers.map((handler) => handler(message.payload, message)));
        const response: RoutedResponse<TMessage> = {
          id: message.id,
          success: true,
          timestamp: Date.now(),
        };
        this.sendResponse(message, response);
        return response;
      } catch (error) {
        const response: RoutedResponse<TMessage> = {
          id: message.id,
          success: false,
          error: error instanceof Error ? error.message : "Unknown error",
          timestamp: Date.now(),
        };
        this.sendResponse(message, response);
        return response;
      }
    }

    // For other targeted messages, call first handler and send response
    try {
      // Track execution to detect double-handler invocation
      globalExecutionTracker.track(message.id, message.payload.type);

      // Check runtime constraints before handler execution
      if (this.stateAccessor) {
        try {
          const { checkPreconditions, isRuntimeConstraintsEnabled } = await import(
            "./constraints.js"
          );
          if (isRuntimeConstraintsEnabled()) {
            const currentState = this.stateAccessor();
            checkPreconditions(message.payload.type, currentState);
          }
        } catch (error) {
          // If constraint check fails, throw immediately
          if (error instanceof Error) {
            throw error;
          }
          // If import fails, log warning but continue (constraints not available)
          if (
            error &&
            typeof error === "object" &&
            "code" in error &&
            error.code === "MODULE_NOT_FOUND"
          ) {
            // Constraints module not available - continue without checking
          } else {
            throw error;
          }
        }
      }

      // We've already checked handlers.length > 0 above, so handlers[0] exists
      const handler = handlers[0];
      if (!handler) {
        throw new Error(`Handler not found for ${message.payload.type}`);
      }
      const data = await handler(message.payload, message);

      // Check postconditions after handler execution (optional)
      if (this.stateAccessor) {
        try {
          const { checkPostconditions, isRuntimeConstraintsEnabled } = await import(
            "./constraints.js"
          );
          if (isRuntimeConstraintsEnabled()) {
            const currentState = this.stateAccessor();
            checkPostconditions(message.payload.type, currentState);
          }
        } catch (error) {
          // Postcondition failures should be logged but not block response
          if (error instanceof Error && error.message.includes("Postcondition")) {
            console.error(`[${this.context}] Postcondition failed:`, error.message);
            // Continue - postcondition failures don't block the response
          }
        }
      }

      const response: RoutedResponse<TMessage> = {
        id: message.id,
        success: true,
        data,
        timestamp: Date.now(),
      };

      this.sendResponse(message, response);
      return response;
    } catch (error) {
      const response: RoutedResponse<TMessage> = {
        id: message.id,
        success: false,
        error: error instanceof Error ? error.message : "Unknown error",
        timestamp: Date.now(),
      };

      this.sendResponse(message, response);
      return response;
    }
  }

  public sendMessage<T extends TMessage = TMessage>(message: RoutedMessage<T>): void {
    if (this.context === "content" && message.targets.includes("page")) {
      // Content → Page via window.postMessage
      this.adapters.window.postMessage({ __extensionMessage: true, message }, "*");
    } else if (this.context === "page") {
      // Page → Content via window.postMessage
      this.adapters.window.postMessage({ __extensionMessage: true, message }, "*");
    } else if (this.port) {
      // Use long-lived port if connected (devtools, content, popup, options)
      this.port.postMessage(message);
    } else {
      // Use chrome.runtime.sendMessage (fallback for unconnected contexts)
      this.adapters.runtime.sendMessage(message);
    }
  }

  private sendResponse(request: RoutedMessage<TMessage>, response: RoutedResponse<TMessage>): void {
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

  private inferTarget(type: string): Context | Context[] | undefined {
    const handlers = {
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
      STATE_SYNC: ALL_CONTEXTS,
      TAB_QUERY: "background",
      TAB_GET_CURRENT: "background",
      TAB_RELOAD: "background",
      LOG: "background",
      LOGS_GET: "background",
      LOGS_CLEAR: "background",
      LOGS_EXPORT: "background",
    } as const;

    // Helper type guard: narrows string to a key of the object
    function isHandlerKey(key: string): key is keyof typeof handlers {
      return key in handlers;
    }

    // Type guard narrows string to known keys
    if (isHandlerKey(type)) {
      // TypeScript now knows type is keyof typeof handlers - no cast needed!
      return handlers[type];
    }

    // Unknown message type - caller must provide explicit target
    return undefined;
  }

  /**
   * Create context-specific helpers based on current context.
   * @private
   */
  private createContextHelpers():
    | ContentScriptHelpers
    | DevToolsHelpers
    | PopupHelpers
    | OptionsHelpers
    | SidePanelHelpers
    | BackgroundHelpers
    | Record<string, never> {
    switch (this.context) {
      case "content":
        return createContentScriptHelpers();
      case "devtools":
        return createDevToolsHelpers();
      case "popup":
        return createPopupHelpers(this.adapters);
      case "options":
        return createOptionsHelpers(this.adapters);
      case "sidepanel":
        return createSidePanelHelpers(this.adapters);
      case "background":
        return createBackgroundHelpers(this.adapters);
      default:
        return {};
    }
  }

  /**
   * Notify all registered error handlers.
   * @private
   */
  private notifyErrorHandlers(error: Error): void {
    for (const handler of this.userErrorHandlers) {
      try {
        handler(error, this);
      } catch (handlerError) {
        console.error(`[${this.context}] Error in error handler:`, handlerError);
      }
    }
  }
}

/**
 * Create a MessageBus for the given context.
 *
 * IMPORTANT: Only call this ONCE per context in your application.
 * Calling it multiple times will create multiple message listeners, causing
 * handlers to execute multiple times. Store the returned bus and reuse it.
 *
 * For background scripts, use createBackground() instead.
 */
export function getMessageBus<TMessage extends BaseMessage = ExtensionMessage>(
  context: Context,
  adapters?: ExtensionAdapters,
  options?: { skipListenerSetup?: boolean }
): MessageBus<TMessage> {
  return new MessageBus<TMessage>(context, adapters, options);
}
