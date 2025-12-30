// Background message router - central hub for all messaging

import type { PortAdapter } from "@/shared/adapters";
import { ErrorHandler, MessageRouterError } from "@/shared/lib/errors";
import {
  getMessageBus,
  isRoutedMessage,
  isRoutedResponse,
  type MessageBus,
} from "@/shared/lib/message-bus";
import type { BaseMessage, Context, RoutedMessage, RoutedResponse } from "@/shared/types/messages";

export class MessageRouter<TMessage extends BaseMessage = BaseMessage> {
  // Singleton enforcement - use boolean to avoid type issues with generic class
  private static instanceExists = false;

  // MessageRouter works with any message type - it just routes them
  private bus: MessageBus<TMessage>;
  private errorHandler: ErrorHandler;

  // Track connections by context and tab
  public contentPorts = new Map<number, PortAdapter>(); // tabId → Port
  public devtoolsPorts = new Map<number, PortAdapter>(); // tabId → Port
  private popupPort: PortAdapter | null = null;
  private optionsPort: PortAdapter | null = null;
  private offscreenPort: PortAdapter | null = null;
  private sidePanelPort: PortAdapter | null = null;

  constructor(bus?: MessageBus<TMessage>) {
    // Enforce singleton pattern to prevent double message handling
    if (MessageRouter.instanceExists) {
      throw new Error(
        "🔴 MessageRouter already exists!\n\n" +
          "Only ONE MessageRouter can exist in the background context.\n" +
          "Multiple MessageRouter instances will cause handlers to execute multiple times.\n\n" +
          "Fix: Ensure createBackground() is only called once at application startup.\n" +
          'Do not call getMessageBus("background") separately - use the bus returned by createBackground().'
      );
    }

    // Mark instance as existing - no cast needed with boolean
    MessageRouter.instanceExists = true;

    // No cast needed - types match now
    this.bus = bus || getMessageBus<TMessage>("background");
    this.errorHandler = new ErrorHandler(this.bus.adapters.logger);
    this.setupPortConnections();
    this.setupTabListeners();
    this.setupMessageHandlers();
  }

  private setupPortConnections(): void {
    this.bus.adapters.runtime.onConnect((port) => {
      this.bus.adapters.logger.debug("Port connected", { port: port.name });

      // Parse port name to determine context and tab
      const [context, tabIdStr] = port.name.split("-");

      switch (context) {
        case "content": {
          const contentTabId = Number.parseInt(tabIdStr || "0", 10);
          if (!Number.isNaN(contentTabId)) {
            this.contentPorts.set(contentTabId, port);
            port.onDisconnect(() => {
              this.bus.adapters.logger.debug("Content port disconnected", {
                tabId: contentTabId,
              });
              this.contentPorts.delete(contentTabId);
            });
          }
          break;
        }

        case "devtools": {
          const devtoolsTabId = Number.parseInt(tabIdStr || "0", 10);
          if (!Number.isNaN(devtoolsTabId)) {
            this.devtoolsPorts.set(devtoolsTabId, port);
            port.onDisconnect(() => {
              this.bus.adapters.logger.debug("DevTools port disconnected", {
                tabId: devtoolsTabId,
              });
              this.devtoolsPorts.delete(devtoolsTabId);
            });
          }
          break;
        }

        case "popup":
          this.popupPort = port;
          port.onDisconnect(() => {
            this.bus.adapters.logger.debug("Popup disconnected");
            this.popupPort = null;
          });
          break;

        case "options":
          this.optionsPort = port;
          port.onDisconnect(() => {
            this.bus.adapters.logger.debug("Options disconnected");
            this.optionsPort = null;
          });
          break;

        case "offscreen":
          this.offscreenPort = port;
          port.onDisconnect(() => {
            this.bus.adapters.logger.debug("Offscreen disconnected");
            this.offscreenPort = null;
          });
          break;

        case "sidepanel":
          this.sidePanelPort = port;
          port.onDisconnect(() => {
            this.bus.adapters.logger.debug("Side panel disconnected");
            this.sidePanelPort = null;
          });
          break;
      }

      // Handle messages from this port
      port.onMessage((message: unknown) => {
        if (isRoutedResponse<TMessage>(message)) {
          // This is a response, route back to original sender
          this.routeResponse(message);
        } else if (isRoutedMessage<TMessage>(message)) {
          // This is a request, route to target
          this.routeMessage(message);
        }
      });
    });
  }

  private setupTabListeners(): void {
    // Clean up ports when tabs are closed
    this.bus.adapters.tabs.onRemoved((tabId) => {
      this.bus.adapters.logger.debug("Tab removed, cleaning up ports", {
        tabId,
      });
      this.contentPorts.delete(tabId);
      this.devtoolsPorts.delete(tabId);
    });

    // Track tab updates
    this.bus.adapters.tabs.onUpdated((tabId, changeInfo, tab) => {
      if (changeInfo.status === "complete") {
        this.bus.adapters.logger.debug("Tab loaded", { tabId, url: tab.url });
      }
    });
  }

  private setupMessageHandlers(): void {
    // Handle messages that need routing
    this.bus.adapters.runtime.onMessage((message: unknown, _sender, sendResponse) => {
      if (isRoutedResponse<TMessage>(message)) {
        this.routeResponse(message);
      } else if (isRoutedMessage<TMessage>(message)) {
        this.routeMessage(message).then(sendResponse);
      }
      return true;
    });
  }

  public async routeMessage(message: RoutedMessage<TMessage>): Promise<unknown> {
    this.bus.adapters.logger.debug("Routing message", {
      type: message.payload.type,
      source: message.source,
      targets: message.targets,
      tabId: message.tabId,
    });

    // Route to each target in the targets array
    const results: unknown[] = [];
    for (const target of message.targets) {
      const result = await this.routeToSingleTarget(message, target);
      results.push(result);
    }

    // If single target, return single result; otherwise return array
    return message.targets.length === 1 ? results[0] : results;
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Message routing requires conditional logic for different targets
  private async routeToSingleTarget(
    message: RoutedMessage<TMessage>,
    target: Context
  ): Promise<unknown> {
    // Route to specific context
    switch (target) {
      case "background":
        // Message is for background, let MessageBus handle it
        return this.bus.handleMessage(message);

      case "content": {
        if (!message.tabId) {
          this.bus.adapters.logger.warn("Content target requires tabId", {
            messageType: message.payload.type,
          });
          return { success: false, error: "tabId required for content target" };
        }
        const contentPort = this.contentPorts.get(message.tabId);
        if (contentPort) {
          contentPort.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("No content script port for tab", {
          tabId: message.tabId,
          messageType: message.payload.type,
        });
        return { success: false, error: "Content script not connected" };
      }

      case "devtools": {
        if (!message.tabId) {
          this.bus.adapters.logger.warn("DevTools target requires tabId", {
            messageType: message.payload.type,
          });
          return {
            success: false,
            error: "tabId required for devtools target",
          };
        }
        const devtoolsPort = this.devtoolsPorts.get(message.tabId);
        if (devtoolsPort) {
          devtoolsPort.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("No DevTools port for tab", {
          tabId: message.tabId,
          messageType: message.payload.type,
        });
        return { success: false, error: "DevTools not connected" };
      }

      case "popup":
        if (this.popupPort) {
          this.popupPort.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("Popup not connected", {
          messageType: message.payload.type,
        });
        return { success: false, error: "Popup not connected" };

      case "options":
        if (this.optionsPort) {
          this.optionsPort.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("Options not connected", {
          messageType: message.payload.type,
        });
        return { success: false, error: "Options not connected" };

      case "offscreen":
        if (this.offscreenPort) {
          this.offscreenPort.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("Offscreen not connected", {
          messageType: message.payload.type,
        });
        return { success: false, error: "Offscreen not connected" };

      case "page": {
        // Page script is not directly connected to background
        // Must route through content script
        if (!message.tabId) {
          this.bus.adapters.logger.warn("Page target requires tabId", {
            messageType: message.payload.type,
          });
          return { success: false, error: "tabId required for page target" };
        }
        const contentPortForPage = this.contentPorts.get(message.tabId);
        if (contentPortForPage) {
          contentPortForPage.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("No content script to forward to page", {
          tabId: message.tabId,
          messageType: message.payload.type,
        });
        return { success: false, error: "Content script not connected" };
      }

      case "sidepanel":
        if (this.sidePanelPort) {
          this.sidePanelPort.postMessage(message);
          return undefined;
        }
        this.bus.adapters.logger.warn("Side panel not connected", {
          messageType: message.payload.type,
        });
        return { success: false, error: "Side panel not connected" };

      default:
        this.bus.adapters.logger.warn("Unknown target context", {
          target,
          messageType: message.payload.type,
        });
        return { success: false, error: `Unknown target context: ${target}` };
    }
  }

  private routeResponse(response: RoutedResponse<TMessage>): void {
    // Responses are handled by MessageBus automatically via pending requests
    this.bus.adapters.logger.debug("Routing response", {
      messageId: response.id,
    });
  }

  // Public API
  async sendToTab(tabId: number, message: RoutedMessage<TMessage>): Promise<void> {
    const port = this.contentPorts.get(tabId);
    if (port) {
      port.postMessage(message);
    } else {
      this.errorHandler.throw(
        new MessageRouterError("No content script connected to tab", {
          tabId,
          messageType: message.payload.type,
        })
      );
    }
  }

  // Broadcast is now just routing with targets array containing all contexts
  broadcastToAll(message: RoutedMessage<TMessage>): void {
    // Message already has targets array, just route it
    this.routeMessage(message);
  }

  isContentScriptConnected(tabId: number): boolean {
    return this.contentPorts.has(tabId);
  }

  getConnectedTabs(): number[] {
    return Array.from(this.contentPorts.keys());
  }

  /**
   * Reset singleton instance. Only for testing purposes.
   * @internal
   */
  static resetInstance(): void {
    MessageRouter.instanceExists = false;
  }
}
