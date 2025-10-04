// Shared application state

import { signal } from "@preact/signals";
import { $sharedState, $syncedState } from "../lib/state";
import type { Settings } from "../types/messages";
import { defaultSettings as _defaultSettings } from "../types/messages";

// Re-export for convenience
export { defaultSettings } from "../types/messages";

// Synced across all contexts, persisted to storage
export const settings = $sharedState<Settings>("app-settings", _defaultSettings);

// Synced but not persisted
export const currentTab = $syncedState<number | null>("current-tab", null);

// Local to each context (not synced) - use regular signal
export const uiState = signal({
  sidebarOpen: false,
  selectedPanel: "main" as "main" | "settings" | "debug",
});
