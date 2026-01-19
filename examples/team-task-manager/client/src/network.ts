// Network state management using Polly patterns
import { computed, signal } from "@preact/signals-core";

/**
 * Online/offline state - Polly-style reactive signal
 * Updates automatically when browser goes online/offline
 */
export const isOnline = signal(typeof navigator !== "undefined" ? navigator.onLine : true);

/**
 * Sync state - tracks whether we're currently syncing queued changes
 */
export const isSyncing = signal(false);

/**
 * Pending sync count - number of changes waiting to be synced
 * In a full Polly implementation, this would track queued requests
 * For now, we track it manually when offline
 */
export const pendingSync = signal(0);

/**
 * Computed: Show sync status message
 */
export const syncStatus = computed(() => {
  if (!isOnline.value) {
    return pendingSync.value > 0 ? `Offline - ${pendingSync.value} changes pending` : "Offline";
  }

  if (isSyncing.value) {
    return `Syncing ${pendingSync.value} changes...`;
  }

  return "Online";
});

/**
 * Setup online/offline listeners
 * Call this once at app initialization
 */
export function setupNetworkListeners(onOnline?: () => void, onOffline?: () => void) {
  if (typeof window === "undefined") {
    return () => {};
  }

  const handleOnline = () => {
    console.log("[Network] Back online");
    isOnline.value = true;
    if (onOnline) onOnline();
  };

  const handleOffline = () => {
    console.log("[Network] Gone offline");
    isOnline.value = false;
    if (onOffline) onOffline();
  };

  window.addEventListener("online", handleOnline);
  window.addEventListener("offline", handleOffline);

  // Return cleanup function
  return () => {
    window.removeEventListener("online", handleOnline);
    window.removeEventListener("offline", handleOffline);
  };
}

/**
 * Increment pending sync count
 * Call this when queueing an offline operation
 */
export function incrementPendingSync() {
  pendingSync.value += 1;
}

/**
 * Decrement pending sync count
 * Call this when a queued operation completes
 */
export function decrementPendingSync() {
  if (pendingSync.value > 0) {
    pendingSync.value -= 1;
  }
}

/**
 * Reset pending sync count
 * Call this after successfully syncing all queued operations
 */
export function resetPendingSync() {
  pendingSync.value = 0;
}
