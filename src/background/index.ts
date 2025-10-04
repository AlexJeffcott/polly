// Background service worker entry point

import { getMessageBus } from "@/shared/lib/message-bus";
import { settings } from "@/shared/state/app-state";
import { APIClient } from "./api-client";
import { ContextMenuManager } from "./context-menu";
import { LogStore } from "./log-store";
import { MessageRouter } from "./message-router";
import { OffscreenManager } from "./offscreen-manager";

// Initialize LogStore FIRST (to collect logs from all other services)
new LogStore();

// Get message bus (now logger is available)
const bus = getMessageBus("background");

// Initialize router and managers
new MessageRouter();
new APIClient();
const contextMenu = new ContextMenuManager();
const offscreen = new OffscreenManager();

// Initialize
async function init() {
  try {
    // Settings are automatically loaded by $sharedState
    // Just wait for initial load to complete
    bus.adapters.logger.info("Settings loaded", {
      settings: settings.value,
    });

    await contextMenu.setup();

    // Ensure offscreen document is created for clipboard operations
    await offscreen.ensureOffscreenDocument();

    bus.adapters.logger.info("Service worker ready");
  } catch (error) {
    bus.adapters.logger.error(
      "Initialization failed",
      error instanceof Error ? error : new Error(String(error))
    );
  }
}

init();

// Handle extension install/update
chrome.runtime.onInstalled.addListener((details) => {
  bus.adapters.logger.info("Extension installed/updated", {
    reason: details.reason,
  });

  if (details.reason === "install") {
    bus.adapters.logger.info("First install");
  } else if (details.reason === "update") {
    bus.adapters.logger.info("Updated to version", {
      version: chrome.runtime.getManifest().version,
    });
  }
});

// Keep service worker alive during development
if (process.env["NODE_ENV"] === "development") {
  setInterval(() => {
    bus.adapters.logger.debug("Keepalive ping");
  }, 20000);
}
