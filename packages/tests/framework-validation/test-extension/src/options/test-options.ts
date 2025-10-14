/**
 * Options Page Example - Example Extension
 *
 * This demonstrates how users would use the framework from an options page context.
 * Options pages are full-page settings interfaces for extensions.
 */

import { createContext } from '@/shared/lib/context-helpers'
import { createTestSuite } from '@/shared/lib/test-helpers'
import type { MessageBus } from '@/shared/lib/message-bus'
import type { AllMessages } from '../shared/types/test-messages'
import { settings } from '@/shared/state/app-state'
import { effect } from '@preact/signals-core'

const bus = createContext<AllMessages>('options', {
  async onInit(bus) {
    registerOptionsHandlers(bus)
    setupOptionsUI(bus)
    setupReactiveUpdates()
    await runOptionsTests(bus)
  },
})

/**
 * Register message handlers for options page
 */
function registerOptionsHandlers(bus: MessageBus<AllMessages>) {
  bus.registerHandlers({
    TEST_STORAGE: async (payload: Extract<AllMessages, { type: 'TEST_STORAGE' }>) => {
      const settingName = 'userPreference'
      const settingValue = payload.testValue || 'default'

      await bus.adapters.storage.set({ [settingName]: settingValue })
      const retrieved = await bus.adapters.storage.get(settingName)

      // Store user preference separately from framework settings
      await bus.adapters.storage.set({ userPreference: settingValue })

      return {
        success: true,
        context: 'options',
        saved: settingValue,
        retrieved: retrieved[settingName],
        matches: retrieved[settingName] === settingValue,
      }
    },

    TEST_SIGNAL_STATE: async () => {
      return {
        success: true,
        context: 'options',
        settings: settings.value,
        timestamp: Date.now(),
      }
    },

    TEST_LOGGER: async (payload: Extract<AllMessages, { type: 'TEST_LOGGER' }>) => {
      const message = payload.message || 'Options page event'
      bus.adapters.logger.info(message, {
        context: 'options',
        currentSettings: settings.value,
      })

      return {
        success: true,
        context: 'options',
        logged: message,
        loggerAvailable: !!bus.adapters.logger,
      }
    },
  })
}

/**
 * Setup options page UI
 */
function setupOptionsUI(bus: MessageBus<AllMessages>) {
  const container = document.getElementById('app') || document.body

  container.innerHTML = `
    <div style="max-width: 800px; margin: 0 auto; padding: 32px; font-family: system-ui;">
      <h1 style="margin-top: 0;">Extension Settings</h1>

      <div style="background: white; padding: 24px; border-radius: 8px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); margin-bottom: 24px;">
        <h2 style="margin-top: 0;">User Preferences</h2>

        <div style="margin-bottom: 16px;">
          <label style="display: block; margin-bottom: 8px; font-weight: 500;">
            Test Setting:
          </label>
          <input
            id="test-setting"
            type="text"
            placeholder="Enter a value..."
            style="width: 100%; padding: 8px; border: 1px solid #ddd; border-radius: 4px; box-sizing: border-box;"
          />
        </div>

        <div style="margin-bottom: 16px;">
          <label style="display: flex; align-items: center; cursor: pointer;">
            <input id="enable-logging" type="checkbox" style="margin-right: 8px;" />
            <span>Enable detailed logging</span>
          </label>
        </div>

        <button
          id="save-settings"
          style="padding: 10px 20px; background: #0066cc; color: white; border: none; border-radius: 4px; cursor: pointer; font-weight: 500;"
        >
          Save Settings
        </button>

        <div id="save-status" style="margin-top: 12px; padding: 8px; border-radius: 4px; display: none;"></div>
      </div>

      <div style="background: white; padding: 24px; border-radius: 8px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); margin-bottom: 24px;">
        <h2 style="margin-top: 0;">Framework Tests</h2>

        <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr)); gap: 12px; margin-bottom: 16px;">
          <button id="test-storage" style="padding: 8px; border: 1px solid #ddd; border-radius: 4px; cursor: pointer; background: white;">
            Test Storage
          </button>
          <button id="test-tabs" style="padding: 8px; border: 1px solid #ddd; border-radius: 4px; cursor: pointer; background: white;">
            Test Tabs
          </button>
          <button id="test-signals" style="padding: 8px; border: 1px solid #ddd; border-radius: 4px; cursor: pointer; background: white;">
            Test Signals
          </button>
          <button id="test-logger" style="padding: 8px; border: 1px solid #ddd; border-radius: 4px; cursor: pointer; background: white;">
            Test Logger
          </button>
        </div>

        <div id="test-results" style="padding: 16px; background: #f5f5f5; border-radius: 4px; min-height: 150px; font-size: 13px;">
          <em>Run tests to see results...</em>
        </div>
      </div>

      <div style="background: #fff3cd; padding: 16px; border-radius: 4px; border-left: 4px solid #ffc107;">
        <strong>Current Settings:</strong>
        <pre id="current-settings" style="margin: 8px 0 0 0; white-space: pre-wrap; word-break: break-all; font-size: 12px;">${JSON.stringify(settings.value, null, 2)}</pre>
      </div>
    </div>
  `

  attachEventListeners(bus)
}

/**
 * Show save confirmation message
 */
function showSaveConfirmation(message: string) {
  const statusDiv = document.getElementById('save-status')
  if (!statusDiv) return

  statusDiv.textContent = message
  statusDiv.style.display = 'block'

  setTimeout(() => {
    statusDiv.style.display = 'none'
  }, 3000)
}

/**
 * Attach event listeners to UI elements
 */
function attachEventListeners(bus: MessageBus<AllMessages>) {
  document.getElementById('save-settings')?.addEventListener('click', async () => {
    const input = document.getElementById('test-setting') as HTMLInputElement
    const checkbox = document.getElementById('enable-logging') as HTMLInputElement
    const statusDiv = document.getElementById('save-status')

    if (!statusDiv) return

    const newSettings = {
      testSetting: input.value,
      enableLogging: checkbox.checked,
      timestamp: Date.now(),
    }

    await bus.adapters.storage.set(newSettings)

    settings.value = { ...settings.value, ...newSettings }

    await bus.sendToBackground({
      type: 'TEST_LOGGER',
      message: `Settings saved: ${JSON.stringify(newSettings)}`,
    })

    showSaveConfirmation('Settings saved successfully!')
  })

  document.getElementById('test-storage')?.addEventListener('click', async () => {
    await runTest(bus, 'Storage', async () => {
      return await bus.sendToBackground({ type: 'TEST_STORAGE', testValue: 'options-test' })
    })
  })

  document.getElementById('test-tabs')?.addEventListener('click', async () => {
    await runTest(bus, 'Tabs', async () => {
      return await bus.sendToBackground({ type: 'TEST_TABS' })
    })
  })

  document.getElementById('test-signals')?.addEventListener('click', async () => {
    await runTest(bus, 'Signals', async () => {
      return await bus.sendToBackground({ type: 'TEST_SIGNAL_STATE' })
    })
  })

  document.getElementById('test-logger')?.addEventListener('click', async () => {
    await runTest(bus, 'Logger', async () => {
      return await bus.sendToBackground({ type: 'TEST_LOGGER', message: 'Options page logger test' })
    })
  })
}

/**
 * Run a test and update UI
 */
async function runTest(
  bus: MessageBus<AllMessages>,
  name: string,
  testFn: () => Promise<unknown>
) {
  const resultsDiv = document.getElementById('test-results')
  if (!resultsDiv) return

  resultsDiv.innerHTML = `<em>Running ${name} test...</em>`

  const result = await testFn()
  resultsDiv.innerHTML = `
    <strong>${name} Test Results:</strong>
    <pre style="margin-top: 8px; white-space: pre-wrap; word-break: break-all;">${JSON.stringify(result, null, 2)}</pre>
  `
}

/**
 * Setup reactive updates
 * Demonstrates how signals automatically update UI across contexts
 */
function setupReactiveUpdates() {
  effect(() => {
    const currentSettingsDiv = document.getElementById('current-settings')
    if (currentSettingsDiv) {
      currentSettingsDiv.textContent = JSON.stringify(settings.value, null, 2)
    }
  })
}

/**
 * Run options page tests
 */
async function runOptionsTests(bus: MessageBus<AllMessages>) {
  const tests = createTestSuite<AllMessages>('options', bus)

  tests.addMessageTest('storage', { type: 'TEST_STORAGE', testValue: 'options-init-test' })
  tests.addMessageTest('signal', { type: 'TEST_SIGNAL_STATE' })
  tests.addMessageTest('tabs', { type: 'TEST_TABS' })
  tests.addMessageTest('logger', { type: 'TEST_LOGGER', message: 'Options page initialization' })

  await tests.run()
}
