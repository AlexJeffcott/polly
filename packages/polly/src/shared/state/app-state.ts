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

const THEMES: readonly Settings["theme"][] = ["light", "dark", "auto"];

/** The theme named by a `<select>` value, or `undefined` when it names none. */
export function readTheme(value: string): Settings["theme"] | undefined {
  return THEMES.find((theme) => theme === value);
}

// Local to each context (not synced) - use regular signal
export const uiState = signal<{
  sidebarOpen: boolean;
  selectedPanel: "main" | "settings" | "debug";
}>({
  sidebarOpen: false,
  selectedPanel: "main",
});
