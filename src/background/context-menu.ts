// Context menu manager

import { type MessageBus, getMessageBus } from "@/shared/lib/message-bus";

export class ContextMenuManager {
  private bus: MessageBus;

  constructor(bus?: MessageBus) {
    this.bus = bus || getMessageBus("background");
    this.setupHandlers();
  }

  async setup(): Promise<void> {
    try {
      // Remove all existing menus
      await this.bus.adapters.contextMenus.removeAll();

      // Create example context menu items
      await this.bus.adapters.contextMenus.create({
        id: "inspect-element",
        title: "Inspect with Extension",
        contexts: ["page", "selection"],
      });

      await this.bus.adapters.contextMenus.create({
        id: "copy-to-clipboard",
        title: "Copy to Clipboard",
        contexts: ["selection"],
      });

      this.bus.adapters.logger.info("Context menus created");
    } catch (error) {
      this.bus.adapters.logger.error(
        "Failed to create context menus",
        error instanceof Error ? error : new Error(String(error))
      );
    }
  }

  private setupHandlers(): void {
    // Listen for context menu clicks
    this.bus.adapters.contextMenus.onClicked((info, tab) => {
      this.bus.adapters.logger.debug("Context menu clicked", {
        menuItemId: info.menuItemId,
        selectionText: info.selectionText,
      });

      if (!tab?.id) return;

      switch (info.menuItemId) {
        case "inspect-element":
          // Send message to content script in the tab
          this.bus
            .send(
              {
                type: "DOM_QUERY",
                selector: "*",
              },
              { target: "content", tabId: tab.id }
            )
            .then((result) => {
              this.bus.adapters.logger.debug("DOM query result", { result });
            })
            .catch((error) => {
              this.bus.adapters.logger.error(
                "DOM query failed",
                error instanceof Error ? error : new Error(String(error))
              );
            });
          break;

        case "copy-to-clipboard":
          if (info.selectionText) {
            // Copy selected text to clipboard via offscreen document
            this.bus
              .send({
                type: "CLIPBOARD_WRITE",
                text: info.selectionText,
              })
              .then(() => {
                this.bus.adapters.logger.info("Copied to clipboard", {
                  text: info.selectionText,
                });
              })
              .catch((error) => {
                this.bus.adapters.logger.error(
                  "Failed to copy to clipboard",
                  error instanceof Error ? error : new Error(String(error))
                );
              });
          }
          break;
      }

      // Broadcast the click event to all contexts
      this.bus.broadcast({
        type: "CONTEXT_MENU_CLICKED",
        menuId: info.menuItemId as string,
        info,
        tabId: tab.id,
      });
    });

    // Handle CONTEXT_MENU_CREATE messages
    this.bus.on("CONTEXT_MENU_CREATE", async (payload) => {
      try {
        await this.bus.adapters.contextMenus.create({
          id: payload.id,
          title: payload.title,
          contexts: payload.contexts,
        });
        return { success: true };
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to create context menu",
          error instanceof Error ? error : new Error(String(error)),
          { menuId: payload.id }
        );
        return { success: false };
      }
    });

    // Handle CONTEXT_MENU_REMOVE messages
    this.bus.on("CONTEXT_MENU_REMOVE", async (payload) => {
      try {
        await this.bus.adapters.contextMenus.remove(payload.id);
        return { success: true };
      } catch (error) {
        this.bus.adapters.logger.error(
          "Failed to remove context menu",
          error instanceof Error ? error : new Error(String(error)),
          { menuId: payload.id }
        );
        return { success: false };
      }
    });
  }
}
