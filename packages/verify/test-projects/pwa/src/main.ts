// Main application file

if ('serviceWorker' in navigator) {
  navigator.serviceWorker.register('/service-worker.js')
    .then(registration => {
      console.log('Service Worker registered:', registration)

      // Send message to service worker
      registration.active?.postMessage({
        type: 'sync',
        data: { timestamp: Date.now() }
      })
    })
    .catch(error => {
      console.error('Service Worker registration failed:', error)
    })
}
