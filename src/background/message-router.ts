// Background message router - central hub for all messaging

import type { PortAdapter } from "@/shared/adapters";
import { ErrorHandler, MessageRouterError } from "@/shared/lib/errors";
import { type MessageBus, getMessageBus } from "@/shared/lib/message-bus";
import type { RoutedMessage, RoutedResponse } from "@/shared/types/messages";

export class MessageRouter {
  private bus: MessageBus;
  private errorHandler: ErrorHandler;

  // Track connections by context and tab
  public contentPorts = new Map<number, PortAdapter>(); // tabId → Port
  public devtoolsPorts = new Map<number, PortAdapter>(); // tabId → Port
  private popupPort: PortAdapter | null = null;
  private optionsPort: PortAdapter | null = null;
  private offscreenPort: PortAdapter | null = null;

  constructor(bus?: MessageBus) {
    this.bus = bus || getMessageBus("background");
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
      }

      // Handle messages from this port
      port.onMessage((message: unknown) => {
        const msg = message as RoutedMessage | RoutedResponse;
        if ("success" in msg) {
          // This is a response, route back to original sender
          this.routeResponse(msg);
        } else {
          // This is a request, route to target
          this.routeMessage(msg);
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
      const msg = message as RoutedMessage | RoutedResponse;
      if ("success" in msg) {
        this.routeResponse(msg);
      } else {
        this.routeMessage(msg).then(sendResponse);
      }
      return true;
    });
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Message routing requires conditional logic for different targets
  public async routeMessage(message: RoutedMessage): Promise<unknown> {
    this.bus.adapters.logger.debug("Routing message", {
      type: message.payload.type,
      source: message.source,
      target: message.target,
      tabId: message.tabId,
    });

    if (message.target === "broadcast") {
      return this.broadcast(message);
    }

    // Route to specific context
    switch (message.target) {
      case "background":
        // Message is for background, let MessageBus handle it
        return;

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
    }
  }

  private routeResponse(response: RoutedResponse): void {
    // Responses are handled by MessageBus automatically via pending requests
    this.bus.adapters.logger.debug("Routing response", {
      messageId: response.id,
    });
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Broadcasting to multiple contexts requires extensive conditional logic
  private broadcast(message: RoutedMessage): void {
    this.bus.adapters.logger.debug("Broadcasting message", {
      type: message.payload.type,
      source: message.source,
    });

    // Send to all content scripts
    for (const [tabId, port] of this.contentPorts.entries()) {
      try {
        port.postMessage(message);
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to broadcast to content script",
          error instanceof Error ? error : new Error(String(error)),
          { tabId, messageType: message.payload.type }
        );
      }
    }

    // Send to all DevTools panels
    for (const [tabId, port] of this.devtoolsPorts.entries()) {
      try {
        port.postMessage(message);
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to broadcast to DevTools",
          error instanceof Error ? error : new Error(String(error)),
          { tabId, messageType: message.payload.type }
        );
      }
    }

    // Send to popup if open
    if (this.popupPort) {
      try {
        this.popupPort.postMessage(message);
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to broadcast to popup",
          error instanceof Error ? error : new Error(String(error)),
          { messageType: message.payload.type }
        );
      }
    }

    // Send to options if open
    if (this.optionsPort) {
      try {
        this.optionsPort.postMessage(message);
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to broadcast to options",
          error instanceof Error ? error : new Error(String(error)),
          { messageType: message.payload.type }
        );
      }
    }

    // Send to offscreen if exists
    if (this.offscreenPort) {
      try {
        this.offscreenPort.postMessage(message);
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to broadcast to offscreen",
          error instanceof Error ? error : new Error(String(error)),
          { messageType: message.payload.type }
        );
      }
    }
  }

  // Public API
  async sendToTab(tabId: number, message: RoutedMessage): Promise<void> {
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

  broadcastToAll(message: RoutedMessage): void {
    this.broadcast(message);
  }

  isContentScriptConnected(tabId: number): boolean {
    return this.contentPorts.has(tabId);
  }

  getConnectedTabs(): number[] {
    return Array.from(this.contentPorts.keys());
  }
}
