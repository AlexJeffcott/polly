// ═══════════════════════════════════════════════════════════════
// Adapter Selection Registry
// ═══════════════════════════════════════════════════════════════
//
// Maps ProjectType to appropriate adapter with sensible defaults.
// Automatically selects the correct adapter based on detected project type.

import type { ProjectType } from "../../analysis/src"
import type { RoutingAdapter } from "./base"
import { WebExtensionAdapter, type WebExtensionAdapterConfig } from "./web-extension"
import { WebSocketAdapter, type WebSocketAdapterConfig } from "./websocket"
import { EventBusAdapter, type EventBusAdapterConfig } from "./event-bus"

/**
 * Adapter factory function type
 */
type AdapterFactory = (tsConfigPath: string) => RoutingAdapter

/**
 * Registry mapping ProjectType to adapter factory functions
 */
export const ADAPTER_REGISTRY: Record<ProjectType, AdapterFactory> = {
  /**
   * Chrome Extension: Uses WebExtensionAdapter with extension-specific contexts
   */
  "chrome-extension": (tsConfigPath: string) => {
    return new WebExtensionAdapter({
      tsConfigPath,
      maxTabs: 1,
      maxInFlight: 3,
      detectTabBased: true,
      contexts: ["background", "content", "popup", "devtools", "options", "offscreen", "sidepanel"],
    })
  },

  /**
   * WebSocket Application: Uses WebSocketAdapter for server-client communication
   */
  "websocket-app": (tsConfigPath: string) => {
    return new WebSocketAdapter({
      tsConfigPath,
      maxConnections: 10,
      maxInFlight: 5,
      useEdenTypes: true,
      handlerPattern: /^handle[A-Z]/,
    })
  },

  /**
   * PWA (Progressive Web App): Uses WebExtensionAdapter with service worker contexts
   * PWAs use similar message passing patterns to extensions (service worker + clients)
   */
  pwa: (tsConfigPath: string) => {
    return new WebExtensionAdapter({
      tsConfigPath,
      maxTabs: 1,
      maxInFlight: 3,
      detectTabBased: false,
      contexts: ["background"], // Service worker acts like background context
    })
  },

  /**
   * Electron Application: Uses EventBusAdapter for IPC communication
   * Electron uses IPC (Inter-Process Communication) between main and renderer processes
   */
  electron: (tsConfigPath: string) => {
    return new EventBusAdapter({
      tsConfigPath,
      maxInFlight: 5,
      maxEmitters: 3,
      emitterPattern: /ipc|electron/i,
      emitterLibrary: "custom",
    })
  },

  /**
   * Generic TypeScript Project: Falls back to detection-based adapter selection
   * Tries to auto-detect the best adapter based on code patterns
   */
  generic: (tsConfigPath: string) => {
    // Import detection module to analyze code patterns
    const { detectAdapter } = require("./detection")
    const result = detectAdapter(tsConfigPath)

    // If detection is confident, use suggested adapter
    if (result.confidence > 50 && result.suggestedAdapter) {
      return result.suggestedAdapter
    }

    // Fallback to EventBusAdapter (most flexible for generic message passing)
    return new EventBusAdapter({
      tsConfigPath,
      maxInFlight: 5,
      maxEmitters: 3,
      emitterPattern: /emitter|bus|events|dispatch|publish/i,
    })
  },
}

/**
 * Select the appropriate adapter for a given project type
 *
 * @param projectType - Detected project type
 * @param tsConfigPath - Path to tsconfig.json
 * @returns Configured RoutingAdapter instance
 *
 * @example
 * const adapter = selectAdapter("websocket-app", "./tsconfig.json")
 * const model = adapter.extractModel()
 */
export function selectAdapter(projectType: ProjectType, tsConfigPath: string): RoutingAdapter {
  const factory = ADAPTER_REGISTRY[projectType]

  if (!factory) {
    throw new Error(
      `No adapter registered for project type "${projectType}". ` +
        `Available types: ${Object.keys(ADAPTER_REGISTRY).join(", ")}`
    )
  }

  return factory(tsConfigPath)
}

/**
 * Get the adapter name for a project type without instantiating
 *
 * @param projectType - Project type to check
 * @returns Adapter name (e.g., "web-extension", "websocket", "event-bus")
 */
export function getAdapterName(projectType: ProjectType): string {
  const adapterNameMap: Record<ProjectType, string> = {
    "chrome-extension": "web-extension",
    "websocket-app": "websocket",
    pwa: "web-extension",
    electron: "event-bus",
    generic: "event-bus (auto-detected)",
  }

  return adapterNameMap[projectType] || "unknown"
}
