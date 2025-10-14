/**
 * Content Script Example - Example Extension
 *
 * This demonstrates how users would use the framework from a content script context.
 * Content scripts run in web pages and can interact with the DOM.
 */

import { createContext } from '@/shared/lib/context-helpers'
import { createTestSuite } from '@/shared/lib/test-helpers'
import type { MessageBus } from '@/shared/lib/message-bus'
import type { AllMessages } from '../shared/types/test-messages'

const bus = createContext<AllMessages>('content', {
  async onInit(bus) {
    registerContentHandlers(bus)
    await runContentTests(bus)
    setupDOMListeners(bus)
  },
})

/**
 * Register message handlers specific to content script
 */
function registerContentHandlers(bus: MessageBus<AllMessages>) {
  bus.registerHandlers({
    TEST_MESSAGE_ROUNDTRIP: async (payload: Extract<AllMessages, { type: 'TEST_MESSAGE_ROUNDTRIP' }>) => {
      return {
        success: true,
        received: payload,
        context: 'content',
        pageInfo: {
          url: window.location.href,
          title: document.title,
          host: window.location.host,
          pathname: window.location.pathname,
          readyState: document.readyState,
        },
      }
    },

    TEST_STORAGE: async (payload: Extract<AllMessages, { type: 'TEST_STORAGE' }>) => {
      const stored = await bus.adapters.storage.get('testKey')

      return {
        success: true,
        context: 'content',
        storedValue: stored.testKey,
        domInfo: {
          bodyClasses: Array.from(document.body.classList),
          hasContent: document.body.children.length > 0,
        },
      }
    },

    TEST_LOGGER: async (payload: Extract<AllMessages, { type: 'TEST_LOGGER' }>) => {
      const message = payload.message || 'Content script log'
      bus.adapters.logger.info(message, { context: 'content', url: window.location.href })

      return {
        success: true,
        logged: message,
        context: 'content',
        loggerAvailable: !!bus.adapters.logger,
      }
    },
  })
}

/**
 * Run content script-specific tests
 */
async function runContentTests(bus: MessageBus<AllMessages>) {
  const tests = createTestSuite('content', bus)

  tests.add('storage', async () => {
    return await bus.sendToBackground({
      type: 'TEST_STORAGE',
      testValue: 'from-content-script',
    })
  })

  tests.add('tabs', async () => {
    return await bus.sendToBackground({ type: 'TEST_TABS' })
  })

  tests.add('logger', async () => {
    return await bus.sendToBackground({
      type: 'TEST_LOGGER',
      message: 'Content script logger test',
    })
  })

  await tests.run()
}

/**
 * Setup DOM event listeners
 * Example: Send messages when user interacts with page
 */
function setupDOMListeners(bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype) {
  document.addEventListener('click', (event) => {
    const target = event.target as HTMLElement

    bus
      .sendToBackground({
        type: 'TEST_MESSAGE_ROUNDTRIP',
        data: {
          type: 'click',
          tagName: target.tagName,
          timestamp: Date.now(),
        },
      })
      .catch(() => {
        // Error handled by global handler
      })
  })

  window.addEventListener('test-framework-event', async (event) => {
    const customEvent = event as CustomEvent

    await bus.sendToBackground({
      type: 'TEST_MESSAGE_ROUNDTRIP',
      data: customEvent.detail,
    })
  })
}
