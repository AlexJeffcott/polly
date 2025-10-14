/**
 * Side Panel Example - Example Extension
 *
 * This demonstrates how users would use the framework from a side panel context.
 * Side panels are persistent companion interfaces that remain open alongside web pages.
 * Available in Chrome 114+.
 */

import { createContext } from '@/shared/lib/context-helpers'
import { createTestSuite } from '@/shared/lib/test-helpers'
import type { MessageBus } from '@/shared/lib/message-bus'
import type { AllMessages } from '../shared/types/test-messages'
import { settings } from '@/shared/state/app-state'
import { effect } from '@preact/signals-core'

const bus = createContext<AllMessages>('sidepanel', {
  async onInit(bus) {
    registerSidePanelHandlers(bus)
    setupSidePanelUI(bus)
    setupRealTimeUpdates(bus)
    await runSidePanelTests(bus)
  },
})

/**
 * Register message handlers for side panel
 */
function registerSidePanelHandlers(bus: MessageBus<AllMessages>) {
  bus.registerHandlers({
    TEST_SIGNAL_STATE: async () => {
      return {
        success: true,
        context: 'sidepanel',
        settings: settings.value,
        panelState: {
          isVisible: document.visibilityState === 'visible',
          width: window.innerWidth,
          height: window.innerHeight,
        },
        timestamp: Date.now(),
      }
    },

    TEST_TABS: async () => {
      const tabs = await bus.adapters.tabs.query({})
      const currentTab = tabs.find((t) => t.active)

      return {
        success: true,
        context: 'sidepanel',
        currentTab: currentTab
          ? {
              id: currentTab.id,
              url: currentTab.url,
              title: currentTab.title,
            }
          : null,
        allTabs: tabs.map((t) => ({
          id: t.id,
          title: t.title,
          active: t.active,
        })),
      }
    },

    TEST_LOGGER: async (payload: Extract<AllMessages, { type: 'TEST_LOGGER' }>) => {
      const message = payload.message || 'Side panel event'

      bus.adapters.logger.info(message, {
        context: 'sidepanel',
        visibility: document.visibilityState,
      })

      return {
        success: true,
        context: 'sidepanel',
        logged: message,
        loggerAvailable: !!bus.adapters.logger,
      }
    },

    TEST_STORAGE: async (payload: Extract<AllMessages, { type: 'TEST_STORAGE' }>) => {
      const panelData = {
        testValue: payload.testValue || 'sidepanel-data',
        preferences: {
          lastActive: Date.now(),
          viewMode: 'default',
        },
      }

      await bus.adapters.storage.set({ panelData })
      const retrieved = await bus.adapters.storage.get('panelData')

      return {
        success: true,
        context: 'sidepanel',
        saved: panelData,
        retrieved: retrieved.panelData,
        matches: JSON.stringify(retrieved.panelData) === JSON.stringify(panelData),
      }
    },
  })
}

/**
 * Setup side panel UI
 */
function setupSidePanelUI(bus: MessageBus<AllMessages>) {
  const container = document.getElementById('app') || document.body

  container.innerHTML = `
    <div style="display: flex; flex-direction: column; height: 100vh; font-family: system-ui; background: #f8f9fa;">
      <!-- Header -->
      <div style="padding: 16px; background: white; border-bottom: 1px solid #dee2e6; box-shadow: 0 1px 3px rgba(0,0,0,0.1);">
        <h2 style="margin: 0; font-size: 18px; color: #212529;">Extension Side Panel</h2>
        <p style="margin: 4px 0 0 0; font-size: 12px; color: #6c757d;">Always-accessible companion panel</p>
      </div>

      <!-- Current Tab Info -->
      <div style="padding: 16px; background: white; border-bottom: 1px solid #dee2e6; margin-bottom: 1px;">
        <div style="font-size: 12px; color: #6c757d; margin-bottom: 4px;">Current Tab</div>
        <div id="current-tab-info" style="font-size: 13px; color: #212529;">
          <em>Loading...</em>
        </div>
      </div>

      <!-- Quick Actions -->
      <div style="padding: 16px; background: white; border-bottom: 1px solid #dee2e6; margin-bottom: 1px;">
        <div style="font-size: 12px; font-weight: 600; color: #495057; margin-bottom: 12px;">Quick Actions</div>
        <div style="display: grid; gap: 8px;">
          <button id="refresh-tab-info" style="padding: 8px; background: #0d6efd; color: white; border: none; border-radius: 4px; cursor: pointer; font-size: 13px;">
            Refresh Tab Info
          </button>
          <button id="test-storage" style="padding: 8px; background: #6c757d; color: white; border: none; border-radius: 4px; cursor: pointer; font-size: 13px;">
            Test Storage
          </button>
          <button id="test-logger" style="padding: 8px; background: #6c757d; color: white; border: none; border-radius: 4px; cursor: pointer; font-size: 13px;">
            Test Logger
          </button>
        </div>
      </div>

      <!-- Activity Log -->
      <div style="flex: 1; padding: 16px; background: white; overflow-y: auto;">
        <div style="font-size: 12px; font-weight: 600; color: #495057; margin-bottom: 12px;">Activity Log</div>
        <div id="activity-log" style="font-size: 12px; font-family: 'Courier New', monospace; color: #495057;">
          <div style="padding: 8px; background: #e7f3ff; border-left: 3px solid #0d6efd; margin-bottom: 8px;">
            Side panel initialized
          </div>
        </div>
      </div>

      <!-- Framework Status -->
      <div style="padding: 12px 16px; background: #f8f9fa; border-top: 1px solid #dee2e6; font-size: 11px; color: #6c757d;">
        <div style="margin-bottom: 4px;">
          <strong>Context:</strong> sidepanel
        </div>
        <div id="settings-status">
          <strong>Settings:</strong> <span id="settings-value">Loading...</span>
        </div>
      </div>
    </div>
  `

  attachSidePanelEventListeners(bus)
  updateCurrentTabInfo(bus)
}

/**
 * Attach event listeners
 */
function attachSidePanelEventListeners(bus: MessageBus<AllMessages>) {
  document.getElementById('refresh-tab-info')?.addEventListener('click', async () => {
    logActivity('Refreshing tab info...', 'info')
    await updateCurrentTabInfo(bus)
  })

  document.getElementById('test-storage')?.addEventListener('click', async () => {
    logActivity('Testing storage...', 'info')
    const result = await bus.sendToBackground({
      type: 'TEST_STORAGE',
      testValue: 'sidepanel-test',
    })
    const status = result && typeof result === 'object' && 'success' in result && result.success
    logActivity(`Storage test: ${status ? 'Success' : 'Failed'}`, status ? 'success' : 'error')
  })

  document.getElementById('test-logger')?.addEventListener('click', async () => {
    logActivity('Testing logger...', 'info')
    const result = await bus.sendToBackground({
      type: 'TEST_LOGGER',
      message: 'Side panel logger test',
    })
    const status = result && typeof result === 'object' && 'success' in result && result.success
    logActivity(`Logger test: ${status ? 'Success' : 'Failed'}`, status ? 'success' : 'error')
  })

  // Listen for tab changes
  if (chrome.tabs?.onActivated) {
    chrome.tabs.onActivated.addListener((activeInfo) => {
      logActivity(`Tab switched to ${activeInfo.tabId}`, 'info')
      updateCurrentTabInfo(bus)
    })
  }

  if (chrome.tabs?.onUpdated) {
    chrome.tabs.onUpdated.addListener((tabId, changeInfo, tab) => {
      if (changeInfo.status === 'complete' && tab.active) {
        logActivity(`Tab updated: ${tab.title}`, 'info')
        updateCurrentTabInfo(bus)
      }
    })
  }
}

/**
 * Update current tab information
 */
async function updateCurrentTabInfo(bus: MessageBus<AllMessages>) {
  const infoEl = document.getElementById('current-tab-info')
  if (!infoEl) return

  const tabs = await bus.adapters.tabs.query({ active: true, currentWindow: true })
  const currentTab = tabs[0]

  if (currentTab) {
    infoEl.innerHTML = `
      <div style="font-weight: 500; margin-bottom: 4px;">${currentTab.title || 'Untitled'}</div>
      <div style="font-size: 11px; color: #6c757d; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;">${currentTab.url || 'No URL'}</div>
    `
    logActivity(`Updated tab info: ${currentTab.title}`, 'success')
  } else {
    infoEl.innerHTML = '<em>No active tab</em>'
  }
}

/**
 * Log activity to the activity log
 */
function logActivity(message: string, type: 'info' | 'success' | 'error' | 'warning' = 'info') {
  const logEl = document.getElementById('activity-log')
  if (!logEl) return

  const colors = {
    info: { bg: '#e7f3ff', border: '#0d6efd' },
    success: { bg: '#d1f0d8', border: '#198754' },
    error: { bg: '#f8d7da', border: '#dc3545' },
    warning: { bg: '#fff3cd', border: '#ffc107' },
  }

  const timestamp = new Date().toLocaleTimeString()
  const entry = document.createElement('div')
  entry.style.cssText = `padding: 8px; background: ${colors[type].bg}; border-left: 3px solid ${colors[type].border}; margin-bottom: 8px; border-radius: 2px;`
  entry.innerHTML = `<span style="color: #6c757d;">[${timestamp}]</span> ${message}`

  logEl.appendChild(entry)
  logEl.scrollTop = logEl.scrollHeight

  while (logEl.children.length > 50) {
    logEl.removeChild(logEl.firstChild!)
  }
}

/**
 * Setup real-time updates
 */
function setupRealTimeUpdates(bus: MessageBus<AllMessages>) {
  effect(() => {
    const settingsValueEl = document.getElementById('settings-value')
    if (settingsValueEl) {
      settingsValueEl.textContent = JSON.stringify(settings.value)
    }
  })

  setInterval(() => {
    updateCurrentTabInfo(bus)
  }, 5000)

  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible') {
      logActivity('Side panel became visible', 'info')
      updateCurrentTabInfo(bus)
    } else {
      logActivity('Side panel hidden', 'info')
    }
  })
}

/**
 * Run side panel tests
 */
async function runSidePanelTests(bus: MessageBus<AllMessages>) {
  const tests = createTestSuite<AllMessages>('sidepanel', bus)

  tests.addMessageTest('storage', { type: 'TEST_STORAGE', testValue: 'sidepanel-init-test' })
  tests.addMessageTest('signal', { type: 'TEST_SIGNAL_STATE' })
  tests.addMessageTest('tabs', { type: 'TEST_TABS' })
  tests.addMessageTest('logger', { type: 'TEST_LOGGER', message: 'Side panel initialization' })

  await tests.run()

  logActivity('All tests completed', 'success')
}
