/**
 * Test Message Handlers - Example Extension
 *
 * This demonstrates how users would add their own message handlers.
 * These handlers exercise the framework to validate it works correctly.
 */

import { createBackground } from '@/background'
import { settings } from '@/shared/state/app-state'
import type { AllMessages } from '../shared/types/test-messages'

const bus = createBackground<AllMessages>()

/**
 * Register test message handlers
 * Users would call this from their background script initialization
 */
export function registerTestHandlers() {
  bus.registerHandlers({
    /**
     * Test handler: Storage read/write
     * Tests: StorageAdapter, async operations
     */
    TEST_STORAGE: async (payload: Extract<AllMessages, { type: 'TEST_STORAGE' }>) => {
      const testData = { testKey: payload.testValue || 'framework-test', timestamp: Date.now() }
      await bus.adapters.storage.set(testData)
      const retrieved = await bus.adapters.storage.get('testKey')

      return {
        success: true,
        written: testData,
        retrieved: retrieved.testKey,
        matches: retrieved.testKey === testData.testKey,
      }
    },

    /**
     * Test handler: Tabs query
     * Tests: TabsAdapter, Chrome tabs API
     */
    TEST_TABS: async () => {
      const tabs = await bus.adapters.tabs.query({})
      const currentTab = tabs.find((t) => t.active)

      return {
        success: true,
        tabCount: tabs.length,
        hasTabs: tabs.length > 0,
        currentTab: currentTab
          ? {
              id: currentTab.id,
              url: currentTab.url,
              title: currentTab.title,
            }
          : null,
      }
    },

    /**
     * Test handler: Message round-trip
     * Tests: MessageBus send/receive, routing
     */
    TEST_MESSAGE_ROUNDTRIP: async (payload: Extract<AllMessages, { type: 'TEST_MESSAGE_ROUNDTRIP' }>) => {
      return {
        success: true,
        received: payload,
        processed: true,
        timestamp: Date.now(),
        context: 'background',
      }
    },

    /**
     * Test handler: State signal access
     * Tests: Signal synchronization, shared state
     */
    TEST_SIGNAL_STATE: async () => {
      return {
        success: true,
        settingsValue: settings.value,
        hasSettings: !!settings.value,
      }
    },

    /**
     * Test handler: Logger adapter
     * Tests: LoggerAdapter, logging infrastructure
     */
    TEST_LOGGER: async (payload: Extract<AllMessages, { type: 'TEST_LOGGER' }>) => {
      const testMessage = payload.message || 'Test log message'

      bus.adapters.logger.info(testMessage, { test: true })
      bus.adapters.logger.debug('Debug test', { level: 'debug' })
      bus.adapters.logger.warn('Warning test', { level: 'warn' })

      return {
        success: true,
        logged: testMessage,
        loggerAvailable: !!bus.adapters.logger,
      }
    },

    /**
     * Test handler: Runtime adapter
     * Tests: RuntimeAdapter, extension metadata
     */
    TEST_RUNTIME: async () => {
      const extensionId = bus.adapters.runtime.getId()
      return {
        success: true,
        extensionId,
        hasId: !!extensionId,
      }
    },

    /**
     * Test handler: Get all test results
     * Tests: Aggregation of all framework tests
     */
    GET_ALL_TEST_RESULTS: async () => {
      const results = {
        timestamp: Date.now(),
        context: 'background',
        tests: {
          storage: await bus.send({ type: 'TEST_STORAGE', testValue: 'end-to-end-test' }),
          tabs: await bus.send({ type: 'TEST_TABS' }),
          roundtrip: await bus.send({
            type: 'TEST_MESSAGE_ROUNDTRIP',
            data: 'test-payload',
          }),
          signal: await bus.send({ type: 'TEST_SIGNAL_STATE' }),
          logger: await bus.send({ type: 'TEST_LOGGER', message: 'Test from validation' }),
          runtime: await bus.send({ type: 'TEST_RUNTIME' }),
        },
      }

      return {
        success: true,
        results,
        allPassed: Object.values(results.tests).every((t) => {
          return typeof t === 'object' && t !== null && 'success' in t && t.success !== false
        }),
      }
    },
  })
}
