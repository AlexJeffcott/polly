// Test fixture: PWA service worker

declare const self: ServiceWorkerGlobalScope;

self.addEventListener("install", (_event) => {
  console.log("Service worker installing...");
});

self.addEventListener("activate", (_event) => {
  console.log("Service worker activating...");
});

self.addEventListener("fetch", (event) => {
  event.respondWith(fetch(event.request));
});

self.addEventListener("message", (event) => {
  console.log("Received message:", event.data);
});
