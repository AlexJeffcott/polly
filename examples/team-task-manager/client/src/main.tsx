import { render } from "preact";
import { App } from "./App";
import "./styles.css";
import { setupNetworkListeners } from "./network";
import { registerServiceWorker, requestPersistentStorage, setupInstallPrompt } from "./pwa";

// Register service worker
registerServiceWorker().then((registration) => {
  if (registration) {
    console.log("Service worker registered successfully");
  }
});

// Setup install prompt
setupInstallPrompt((prompt) => {
  console.log("Install prompt is available");
  // The install button will be shown in the UI when needed
});

// Setup online/offline listeners using Polly patterns
setupNetworkListeners(
  () => {
    console.log("Back online - syncing data...");
    // Trigger sync when back online
    window.dispatchEvent(new CustomEvent("online-sync"));
  },
  () => {
    console.log("Offline mode - data will sync when reconnected");
  }
);

// Request persistent storage to prevent data eviction
requestPersistentStorage().then((granted) => {
  if (granted) {
    console.log("Persistent storage granted");
  }
});

const root = document.getElementById("root");
if (root) {
  render(<App />, root);
}
