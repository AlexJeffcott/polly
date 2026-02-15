// PWA utilities and service worker registration

export interface BeforeInstallPromptEvent extends Event {
  prompt(): Promise<void>;
  userChoice: Promise<{ outcome: "accepted" | "dismissed" }>;
}

let deferredPrompt: BeforeInstallPromptEvent | null = null;

/**
 * Register the service worker
 */
export async function registerServiceWorker(): Promise<ServiceWorkerRegistration | null> {
  if (!("serviceWorker" in navigator)) {
    console.log("Service workers not supported");
    return null;
  }

  try {
    const registration = await navigator.serviceWorker.register("/service-worker.js", {
      scope: "/",
    });

    console.log("Service worker registered:", registration);

    // Check for updates periodically
    setInterval(() => {
      registration.update();
    }, 60000); // Check every minute

    // Listen for updates
    registration.addEventListener("updatefound", () => {
      const newWorker = registration.installing;
      if (!newWorker) return;

      newWorker.addEventListener("statechange", () => {
        if (newWorker.state === "installed" && navigator.serviceWorker.controller) {
          // New service worker available
          console.log("New service worker available");

          // Notify user about update
          if (confirm("A new version is available. Reload to update?")) {
            newWorker.postMessage({ type: "SKIP_WAITING" });
            window.location.reload();
          }
        }
      });
    });

    return registration;
  } catch (error) {
    console.error("Service worker registration failed:", error);
    return null;
  }
}

/**
 * Unregister the service worker (for development)
 */
export async function unregisterServiceWorker(): Promise<boolean> {
  if (!("serviceWorker" in navigator)) {
    return false;
  }

  try {
    const registration = await navigator.serviceWorker.getRegistration();
    if (registration) {
      return await registration.unregister();
    }
    return false;
  } catch (error) {
    console.error("Service worker unregistration failed:", error);
    return false;
  }
}

/**
 * Check if app is installed (running as PWA)
 */
export function isPWA(): boolean {
  return (
    window.matchMedia("(display-mode: standalone)").matches ||
    (window.navigator as any).standalone === true ||
    document.referrer.includes("android-app://")
  );
}

/**
 * Setup install prompt capture
 */
export function setupInstallPrompt(
  onPromptAvailable?: (prompt: BeforeInstallPromptEvent) => void
): void {
  window.addEventListener("beforeinstallprompt", (e) => {
    // Prevent the mini-infobar from appearing
    e.preventDefault();

    // Stash the event so it can be triggered later
    deferredPrompt = e as BeforeInstallPromptEvent;

    console.log("Install prompt available");

    if (onPromptAvailable) {
      onPromptAvailable(deferredPrompt);
    }
  });

  window.addEventListener("appinstalled", () => {
    console.log("PWA installed");
    deferredPrompt = null;
  });
}

/**
 * Show the install prompt
 */
export async function showInstallPrompt(): Promise<"accepted" | "dismissed" | "unavailable"> {
  if (!deferredPrompt) {
    return "unavailable";
  }

  try {
    await deferredPrompt.prompt();
    const choiceResult = await deferredPrompt.userChoice;

    deferredPrompt = null;

    return choiceResult.outcome;
  } catch (error) {
    console.error("Install prompt failed:", error);
    return "unavailable";
  }
}

/**
 * Check if install prompt is available
 */
export function isInstallPromptAvailable(): boolean {
  return deferredPrompt !== null;
}

/**
 * Request notification permission
 */
export async function requestNotificationPermission(): Promise<NotificationPermission> {
  if (!("Notification" in window)) {
    console.log("Notifications not supported");
    return "denied";
  }

  if (Notification.permission === "granted") {
    return "granted";
  }

  if (Notification.permission === "denied") {
    return "denied";
  }

  return await Notification.requestPermission();
}

/**
 * Show a notification
 */
export async function showNotification(
  title: string,
  options?: NotificationOptions
): Promise<void> {
  if (!("serviceWorker" in navigator)) {
    return;
  }

  const registration = await navigator.serviceWorker.getRegistration();
  if (!registration) {
    return;
  }

  const permission = await requestNotificationPermission();
  if (permission !== "granted") {
    return;
  }

  await registration.showNotification(title, {
    icon: "/icons/icon-192x192.png",
    badge: "/icons/icon-72x72.png",
    ...options,
  });
}

/**
 * Check if the app is online
 */
export function isOnline(): boolean {
  return navigator.onLine;
}

/**
 * Setup online/offline listeners
 */
export function setupOnlineListeners(onOnline?: () => void, onOffline?: () => void): () => void {
  const handleOnline = () => {
    console.log("App is online");
    if (onOnline) onOnline();
  };

  const handleOffline = () => {
    console.log("App is offline");
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
 * Get storage estimate
 */
export async function getStorageEstimate(): Promise<{
  usage: number;
  quota: number;
  percentage: number;
} | null> {
  if (!("storage" in navigator) || !("estimate" in navigator.storage)) {
    return null;
  }

  try {
    const estimate = await navigator.storage.estimate();
    const usage = estimate.usage || 0;
    const quota = estimate.quota || 0;
    const percentage = quota > 0 ? (usage / quota) * 100 : 0;

    return { usage, quota, percentage };
  } catch (error) {
    console.error("Failed to get storage estimate:", error);
    return null;
  }
}

/**
 * Request persistent storage
 */
export async function requestPersistentStorage(): Promise<boolean> {
  if (!("storage" in navigator) || !("persist" in navigator.storage)) {
    return false;
  }

  try {
    const isPersisted = await navigator.storage.persisted();
    if (isPersisted) {
      return true;
    }

    return await navigator.storage.persist();
  } catch (error) {
    console.error("Failed to request persistent storage:", error);
    return false;
  }
}
