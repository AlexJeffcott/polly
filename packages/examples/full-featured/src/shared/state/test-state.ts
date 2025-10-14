/**
 * Test State
 *
 * This demonstrates how users would create their own state using the framework's primitives.
 * Imports from the installed framework package.
 */

import { $sharedState, $syncedState } from "@fairfox/web-ext/state";
import { signal } from "@preact/signals";

// SIMPLE TEST: just a number
export const simpleSharedCounter = $sharedState("simple-shared", 0);
export const simpleSyncedCounter = $syncedState("simple-synced", 0);

// Test $sharedState (syncs across contexts + persists to storage)
export const testCounter = $sharedState("test-counter", 0);

export const testPreferences = $sharedState("test-preferences", {
  color: "blue" as "blue" | "red" | "green",
  size: "medium" as "small" | "medium" | "large",
  enabled: true,
});

// Test $syncedState (syncs across contexts, doesn't persist)
export const testMessage = $syncedState("test-message", "");

export const testActiveTab = $syncedState<number | null>("test-active-tab", null);

// Test local signal (no sync, no persist - context-specific)
export const testLocalCounter = signal(0);

// Test results (synced so all contexts see results)
export const testResults = $syncedState<Record<string, any>>("test-results", {});

export const testStatus = $syncedState<"idle" | "running" | "success" | "error">(
  "test-status",
  "idle"
);
