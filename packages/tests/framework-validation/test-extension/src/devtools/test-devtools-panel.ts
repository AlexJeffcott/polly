/**
 * DevTools Panel Example - Example Extension
 *
 * This demonstrates how users would use the framework from a DevTools panel context.
 * DevTools panels appear in the Chrome DevTools interface and can inspect page state.
 */

import { createContext } from '@/shared/lib/context-helpers'
import { createTestSuite } from '@/shared/lib/test-helpers'
import type { MessageBus } from '@/shared/lib/message-bus'
import type { AllMessages } from '../shared/types/test-messages'
import '../shared/types/window'

const bus = createContext<AllMessages>('devtools', {
  async onInit(bus) {
    registerDevToolsHandlers(bus)
    setupDevToolsUI(bus)
    setupInspectedWindowBridge()
    await runDevToolsTests(bus)
  },
})

/**
 * Register message handlers for DevTools panel
 */
function registerDevToolsHandlers(bus: MessageBus<AllMessages>) {
  const inspectedTabId = chrome.devtools?.inspectedWindow?.tabId

  bus.registerHandlers({
    TEST_TABS: async () => {
      return {
        success: true,
        context: 'devtools',
        inspectedTabId,
        inspectedUrl: await getInspectedPageURL(),
        timestamp: Date.now(),
      }
    },

    TEST_LOGGER: async (payload: Extract<AllMessages, { type: 'TEST_LOGGER' }>) => {
      const message = payload.message || 'DevTools inspection log'

      bus.adapters.logger.info(message, {
        context: 'devtools',
        tabId: inspectedTabId,
      })

      return {
        success: true,
        context: 'devtools',
        logged: message,
        loggerAvailable: !!bus.adapters.logger,
      }
    },

    TEST_STORAGE: async (payload: Extract<AllMessages, { type: 'TEST_STORAGE' }>) => {
      const inspectionData = {
        testValue: payload.testValue || 'devtools-inspection',
        tabId: inspectedTabId,
        timestamp: Date.now(),
      }

      await bus.adapters.storage.set({ inspectionData })
      const retrieved = await bus.adapters.storage.get('inspectionData')

      return {
        success: true,
        context: 'devtools',
        saved: inspectionData,
        retrieved: retrieved.inspectionData,
        matches: JSON.stringify(retrieved.inspectionData) === JSON.stringify(inspectionData),
      }
    },
  })
}

/**
 * Get inspected page URL
 */
async function getInspectedPageURL(): Promise<string> {
  return new Promise((resolve) => {
    if (!chrome.devtools?.inspectedWindow) {
      resolve('unknown')
      return
    }

    chrome.devtools.inspectedWindow.eval('window.location.href', (result, error) => {
      if (error) {
        resolve('error')
      } else {
        resolve(result as string)
      }
    })
  })
}

/**
 * Setup DevTools panel UI
 */
function setupDevToolsUI(bus: MessageBus<AllMessages>) {
  const container = document.getElementById('app') || document.body

  container.innerHTML = `
    <div style="padding: 16px; font-family: system-ui; height: 100vh; background: #1e1e1e; color: #d4d4d4; overflow: auto;">
      <h2 style="margin-top: 0; color: #569cd6;">Extension Framework Inspector</h2>

      <div style="background: #252526; padding: 16px; border-radius: 4px; margin-bottom: 16px;">
        <h3 style="margin-top: 0; color: #4ec9b0;">Inspected Page</h3>
        <div style="font-family: 'Courier New', monospace; font-size: 12px;">
          <div style="margin-bottom: 8px;">
            <span style="color: #9cdcfe;">Tab ID:</span>
            <span id="tab-id" style="color: #ce9178;">Loading...</span>
          </div>
          <div style="margin-bottom: 8px;">
            <span style="color: #9cdcfe;">URL:</span>
            <span id="page-url" style="color: #ce9178;">Loading...</span>
          </div>
        </div>
      </div>

      <div style="background: #252526; padding: 16px; border-radius: 4px; margin-bottom: 16px;">
        <h3 style="margin-top: 0; color: #4ec9b0;">Framework Actions</h3>
        <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(120px, 1fr)); gap: 8px; margin-bottom: 12px;">
          <button id="inspect-page" style="padding: 8px; background: #0e639c; color: white; border: none; border-radius: 3px; cursor: pointer; font-size: 12px;">
            Inspect Page
          </button>
          <button id="test-storage" style="padding: 8px; background: #0e639c; color: white; border: none; border-radius: 3px; cursor: pointer; font-size: 12px;">
            Test Storage
          </button>
          <button id="test-logger" style="padding: 8px; background: #0e639c; color: white; border: none; border-radius: 3px; cursor: pointer; font-size: 12px;">
            Test Logger
          </button>
          <button id="run-all-tests" style="padding: 8px; background: #14a653; color: white; border: none; border-radius: 3px; cursor: pointer; font-size: 12px; font-weight: bold;">
            Run All Tests
          </button>
        </div>

        <div style="background: #1e1e1e; padding: 12px; border-radius: 3px; border-left: 3px solid #0e639c;">
          <div style="color: #6a9955; font-size: 11px; margin-bottom: 4px;">// Console Output</div>
          <div id="console-output" style="font-family: 'Courier New', monospace; font-size: 11px; max-height: 150px; overflow-y: auto; color: #d4d4d4;">
            <em style="color: #858585;">No output yet...</em>
          </div>
        </div>
      </div>

      <div style="background: #252526; padding: 16px; border-radius: 4px;">
        <h3 style="margin-top: 0; color: #4ec9b0;">Test Results</h3>
        <div id="test-results" style="background: #1e1e1e; padding: 12px; border-radius: 3px; font-family: 'Courier New', monospace; font-size: 11px; max-height: 300px; overflow-y: auto; white-space: pre-wrap; word-break: break-all;">
          <em style="color: #858585;">Run tests to see results...</em>
        </div>
      </div>
    </div>
  `

  updateInspectedPageInfo(bus)
  attachDevToolsEventListeners(bus)
}

/**
 * Update inspected page information
 */
async function updateInspectedPageInfo(bus: MessageBus<AllMessages>) {
  const tabIdEl = document.getElementById('tab-id')
  const pageUrlEl = document.getElementById('page-url')
  const inspectedTabId = chrome.devtools?.inspectedWindow?.tabId

  if (tabIdEl && inspectedTabId) {
    tabIdEl.textContent = String(inspectedTabId)
  }

  if (pageUrlEl) {
    const url = await getInspectedPageURL()
    pageUrlEl.textContent = url
  }
}

/**
 * Attach event listeners
 */
function attachDevToolsEventListeners(bus: MessageBus<AllMessages>) {
  document.getElementById('inspect-page')?.addEventListener('click', async () => {
    await runDevToolsTest(bus, 'Inspect Page', async () => {
      const pageData = await evalInInspectedPage(`
        ({
          url: window.location.href,
          title: document.title,
          bodyClasses: Array.from(document.body.classList),
          elementCount: document.body.querySelectorAll('*').length,
          timestamp: Date.now()
        })
      `)

      return {
        success: true,
        context: 'devtools',
        pageData,
      }
    })
  })

  document.getElementById('test-storage')?.addEventListener('click', async () => {
    await runDevToolsTest(bus, 'Storage', async () => {
      return await bus.sendToBackground({ type: 'TEST_STORAGE', testValue: 'devtools-test' })
    })
  })

  document.getElementById('test-logger')?.addEventListener('click', async () => {
    await runDevToolsTest(bus, 'Logger', async () => {
      return await bus.sendToBackground({ type: 'TEST_LOGGER', message: 'DevTools logger test' })
    })
  })

  document.getElementById('run-all-tests')?.addEventListener('click', async () => {
    await runAllDevToolsTests(bus)
  })
}

/**
 * Evaluate code in the inspected page
 */
async function evalInInspectedPage<T>(code: string): Promise<T> {
  return new Promise((resolve, reject) => {
    if (!chrome.devtools?.inspectedWindow) {
      reject(new Error('DevTools inspectedWindow not available'))
      return
    }

    chrome.devtools.inspectedWindow.eval(code, (result, error) => {
      if (error) {
        reject(new Error(error.value || 'Eval error'))
      } else {
        resolve(result as T)
      }
    })
  })
}

/**
 * Run a single DevTools test
 */
async function runDevToolsTest(
  bus: MessageBus<AllMessages>,
  name: string,
  testFn: () => Promise<unknown>
) {
  const resultsDiv = document.getElementById('test-results')
  const consoleDiv = document.getElementById('console-output')

  if (consoleDiv) {
    addConsoleMessage(consoleDiv, `Running ${name} test...`, 'info')
  }

  if (resultsDiv) {
    resultsDiv.innerHTML = `<em style="color: #858585;">Running ${name} test...</em>`
  }

  const result = await testFn()

  if (resultsDiv) {
    resultsDiv.textContent = JSON.stringify(result, null, 2)
  }

  if (consoleDiv) {
    addConsoleMessage(consoleDiv, `${name} test completed successfully`, 'success')
  }
}

/**
 * Add console message
 */
function addConsoleMessage(consoleDiv: HTMLElement, message: string, type: 'info' | 'success' | 'error') {
  const colors = {
    info: '#9cdcfe',
    success: '#4ec9b0',
    error: '#f48771',
  }

  const timestamp = new Date().toLocaleTimeString()
  const line = document.createElement('div')
  line.innerHTML = `<span style="color: #858585;">[${timestamp}]</span> <span style="color: ${colors[type]};">${message}</span>`

  if (consoleDiv.querySelector('em')) {
    consoleDiv.innerHTML = ''
  }

  consoleDiv.appendChild(line)
  consoleDiv.scrollTop = consoleDiv.scrollHeight
}

/**
 * Setup communication bridge with inspected window
 */
function setupInspectedWindowBridge() {
  if (chrome.devtools?.inspectedWindow) {
    // Bridge established
  }
}

/**
 * Run all DevTools tests
 */
async function runAllDevToolsTests(bus: MessageBus<AllMessages>) {
  const resultsDiv = document.getElementById('test-results')
  const consoleDiv = document.getElementById('console-output')
  const inspectedTabId = chrome.devtools?.inspectedWindow?.tabId

  if (consoleDiv) {
    addConsoleMessage(consoleDiv, 'Starting all tests...', 'info')
  }

  const results = {
    timestamp: Date.now(),
    context: 'devtools',
    tabId: inspectedTabId,
    tests: {} as Record<string, unknown>,
  }

  results.tests.storage = await bus.sendToBackground({ type: 'TEST_STORAGE', testValue: 'devtools-all-test' })
  results.tests.tabs = await bus.sendToBackground({ type: 'TEST_TABS' })
  results.tests.logger = await bus.sendToBackground({ type: 'TEST_LOGGER', message: 'DevTools all tests' })

  results.tests.inspectedPage = await evalInInspectedPage(`
    ({
      url: window.location.href,
      title: document.title,
      readyState: document.readyState
    })
  `)

  if (resultsDiv) {
    resultsDiv.textContent = JSON.stringify(results, null, 2)
  }

  if (consoleDiv) {
    addConsoleMessage(consoleDiv, 'All tests completed successfully', 'success')
  }

  window.__DEVTOOLS_TEST_RESULTS__ = results
}

/**
 * Run DevTools panel tests
 */
async function runDevToolsTests(bus: MessageBus<AllMessages>) {
  const tests = createTestSuite<AllMessages>('devtools', bus)

  tests.addMessageTest('storage', { type: 'TEST_STORAGE', testValue: 'devtools-init-test' })
  tests.addMessageTest('tabs', { type: 'TEST_TABS' })
  tests.addMessageTest('logger', { type: 'TEST_LOGGER', message: 'DevTools panel initialization' })

  await tests.run()
}
