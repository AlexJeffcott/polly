/**
 * Popup Example - Example Extension
 *
 * This demonstrates how users would use the framework from a popup context.
 * Popups are short-lived UI windows that appear when users click the extension icon.
 */

import { createContext } from '@/shared/lib/context-helpers'
import { createTestSuite } from '@/shared/lib/test-helpers'
import { settings } from '@/shared/state/app-state'
import '../shared/types/window'

const bus = createContext('popup', {
  async onInit(bus) {
    registerPopupHandlers(bus)
    setupUI(bus)
    await runPopupTests(bus)
  },
})

/**
 * Register message handlers for popup
 */
function registerPopupHandlers(bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype) {
  bus.registerHandlers({
    TEST_SIGNAL_STATE: async () => {
      return {
        success: true,
        context: 'popup',
        settingsValue: settings.value,
        uiState: {
          isVisible: document.visibilityState === 'visible',
          dimensions: {
            width: window.innerWidth,
            height: window.innerHeight,
          },
        },
      }
    },

    GET_ALL_TEST_RESULTS: async () => {
      const results = await bus.sendToBackground({ type: 'GET_ALL_TEST_RESULTS' })

      updateUIWithResults(results)

      return {
        success: true,
        context: 'popup',
        forwarded: true,
        results,
      }
    },
  })
}

/**
 * Setup popup UI
 */
function setupUI(bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype) {
  const container = document.getElementById('app') || document.body

  container.innerHTML = `
    <div style="padding: 16px; min-width: 300px; font-family: system-ui;">
      <h2 style="margin-top: 0;">Extension Framework Test</h2>

      <div style="margin-bottom: 16px;">
        <button id="test-storage" style="width: 100%; padding: 8px; margin-bottom: 8px;">
          Test Storage
        </button>
        <button id="test-tabs" style="width: 100%; padding: 8px; margin-bottom: 8px;">
          Test Tabs
        </button>
        <button id="test-logger" style="width: 100%; padding: 8px; margin-bottom: 8px;">
          Test Logger
        </button>
        <button id="run-all-tests" style="width: 100%; padding: 8px; background: #0066cc; color: white; font-weight: bold;">
          Run All Tests
        </button>
      </div>

      <div id="results" style="padding: 12px; background: #f5f5f5; border-radius: 4px; min-height: 100px; font-size: 12px; overflow-y: auto; max-height: 300px;">
        <em>Click a button to run tests...</em>
      </div>

      <div style="margin-top: 12px; padding: 8px; background: #e3f2fd; border-radius: 4px; font-size: 11px;">
        <strong>Context:</strong> Popup<br>
        <strong>Settings:</strong> ${JSON.stringify(settings.value)}
      </div>
    </div>
  `

  attachEventListeners(bus)
}

/**
 * Attach event listeners to UI elements
 */
function attachEventListeners(bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype) {
  document.getElementById('test-storage')?.addEventListener('click', async () => {
    await runTest(bus, 'storage', async () => {
      return await bus.sendToBackground({ type: 'TEST_STORAGE', testValue: 'from-popup' })
    })
  })

  document.getElementById('test-tabs')?.addEventListener('click', async () => {
    await runTest(bus, 'tabs', async () => {
      return await bus.sendToBackground({ type: 'TEST_TABS' })
    })
  })

  document.getElementById('test-logger')?.addEventListener('click', async () => {
    await runTest(bus, 'logger', async () => {
      return await bus.sendToBackground({ type: 'TEST_LOGGER', message: 'Popup logger test' })
    })
  })

  document.getElementById('run-all-tests')?.addEventListener('click', async () => {
    await runAllTests(bus)
  })
}

/**
 * Run a single test and update UI
 */
async function runTest(
  bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype,
  name: string,
  testFn: () => Promise<any>
) {
  const resultsDiv = document.getElementById('results')
  if (!resultsDiv) return

  resultsDiv.innerHTML = `<em>Running ${name} test...</em>`

  const result = await testFn()
  resultsDiv.innerHTML = `
    <strong>${name} Test Results:</strong>
    <pre style="margin-top: 8px; white-space: pre-wrap; word-break: break-all;">${JSON.stringify(result, null, 2)}</pre>
  `
}

/**
 * Run all tests
 */
async function runAllTests(bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype) {
  const resultsDiv = document.getElementById('results')
  if (!resultsDiv) return

  resultsDiv.innerHTML = '<em>Running all tests...</em>'

  const results = await bus.sendToBackground({ type: 'GET_ALL_TEST_RESULTS' })

  updateUIWithResults(results)

  window.__POPUP_TEST_RESULTS__ = results
}

/**
 * Update UI with test results
 */
function updateUIWithResults(results: any) {
  const resultsDiv = document.getElementById('results')
  if (!resultsDiv) return

  const allPassed = results.allPassed || results.success
  const statusColor = allPassed ? 'green' : 'red'
  const statusText = allPassed ? 'All tests passed!' : 'Some tests failed'

  resultsDiv.innerHTML = `
    <strong style="color: ${statusColor};">${statusText}</strong>
    <pre style="margin-top: 8px; white-space: pre-wrap; word-break: break-all; font-size: 11px;">${JSON.stringify(results, null, 2)}</pre>
  `
}

/**
 * Run popup-specific tests
 */
async function runPopupTests(bus: typeof import('@/shared/lib/message-bus').MessageBus.prototype) {
  const tests = createTestSuite('popup', bus)

  tests.addMessageTest('storage', { type: 'TEST_STORAGE', testValue: 'popup-init-test' })
  tests.addMessageTest('signal', { type: 'TEST_SIGNAL_STATE' })
  tests.addMessageTest('logger', { type: 'TEST_LOGGER', message: 'Popup initialization log' })

  await tests.run()
}
