/// <reference lib="WebWorker" />

declare const self: ServiceWorkerGlobalScope

interface SyncMessage {
  type: 'sync'
  data: unknown
}

interface CacheMessage {
  type: 'cache'
  url: string
}

type WorkerMessage = SyncMessage | CacheMessage

self.addEventListener('message', (event) => {
  const message = event.data as WorkerMessage

  if (message.type === 'sync') {
    // Handle sync
    console.log('Syncing data:', message.data)
  } else if (message.type === 'cache') {
    // Handle cache
    console.log('Caching URL:', message.url)
  }
})

self.addEventListener('fetch', (event) => {
  // Simple fetch handling
  event.respondWith(fetch(event.request))
})
