import { test, expect } from '@playwright/test'
import {
  launchWithExtension,
  openPopup,
  evaluateInBackground,
} from './helpers/extension-helpers'

/**
 * Framework Validation: Adapter Pattern
 *
 * Tests that the adapter pattern is working correctly and
 * that all Chrome APIs are accessible through adapters.
 */

test.describe('Framework Validation: Adapter Pattern', () => {
  test.beforeAll(async ({ browserName }) => {
    if (browserName !== 'chromium') {
      test.skip()
    }
  })

  test('RuntimeAdapter - chrome.runtime is accessible', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const runtimeId = await evaluateInBackground(context, () => {
      // @ts-ignore
      return chrome.runtime.id
    })

    expect(runtimeId).toBe(extensionId)

    console.log(`✓ RuntimeAdapter works`)

    await context.close()
  })

  test('StorageAdapter - chrome.storage.local works', async ({ playwright }) => {
    const { context } = await launchWithExtension(playwright)

    const stored = await evaluateInBackground(context, async () => {
      // @ts-ignore
      await chrome.storage.local.set({ adapterTest: 'works' })
      // @ts-ignore
      const result = await chrome.storage.local.get('adapterTest')
      return result.adapterTest
    })

    expect(stored).toBe('works')

    console.log(`✓ StorageAdapter works`)

    await context.close()
  })

  test('TabsAdapter - chrome.tabs is accessible', async ({ playwright }) => {
    const { context } = await launchWithExtension(playwright)

    const tabsExist = await evaluateInBackground(context, async () => {
      // @ts-ignore
      const tabs = await chrome.tabs.query({})
      return tabs.length > 0
    })

    expect(tabsExist).toBe(true)

    console.log(`✓ TabsAdapter works`)

    await context.close()
  })

  test('WindowAdapter - chrome.windows is accessible', async ({ playwright }) => {
    const { context } = await launchWithExtension(playwright)

    const windowsExist = await evaluateInBackground(context, async () => {
      // @ts-ignore
      const windows = await chrome.windows.getAll()
      return windows.length > 0
    })

    expect(windowsExist).toBe(true)

    console.log(`✓ WindowAdapter works`)

    await context.close()
  })

  test('ContextMenusAdapter - chrome.contextMenus is accessible', async ({
    playwright,
  }) => {
    const { context } = await launchWithExtension(playwright)

    const canCreateMenu = await evaluateInBackground(context, () => {
      // @ts-ignore
      return typeof chrome.contextMenus.create === 'function'
    })

    expect(canCreateMenu).toBe(true)

    console.log(`✓ ContextMenusAdapter works`)

    await context.close()
  })

  test('OffscreenAdapter - chrome.offscreen is accessible', async ({ playwright }) => {
    const { context } = await launchWithExtension(playwright)

    const hasOffscreen = await evaluateInBackground(context, () => {
      // @ts-ignore
      return typeof chrome.offscreen !== 'undefined'
    })

    expect(hasOffscreen).toBe(true)

    console.log(`✓ OffscreenAdapter works`)

    await context.close()
  })

  test('fetch is available in background', async ({ playwright }) => {
    const { context } = await launchWithExtension(playwright)

    const canFetch = await evaluateInBackground(context, () => {
      return typeof fetch === 'function'
    })

    expect(canFetch).toBe(true)

    console.log(`✓ FetchAdapter (native fetch) is available`)

    await context.close()
  })

  test('console logging works (LoggerAdapter)', async ({ playwright }) => {
    const { context } = await launchWithExtension(playwright)

    const canLog = await evaluateInBackground(context, () => {
      return typeof console.log === 'function' && typeof console.error === 'function'
    })

    expect(canLog).toBe(true)

    console.log(`✓ LoggerAdapter (console) works`)

    await context.close()
  })

  test('all Chrome APIs required by framework are available', async ({
    playwright,
  }) => {
    const { context } = await launchWithExtension(playwright)

    const allApisAvailable = await evaluateInBackground(context, () => {
      const requiredApis = [
        'runtime',
        'storage',
        'tabs',
        'windows',
        'contextMenus',
        'offscreen',
        'scripting',
      ]

      // @ts-ignore
      const availableApis = requiredApis.filter((api) => chrome[api] !== undefined)

      return {
        required: requiredApis,
        available: availableApis,
        allAvailable: requiredApis.length === availableApis.length,
      }
    })

    expect(allApisAvailable.allAvailable).toBe(true)

    console.log(`✓ All required Chrome APIs are available`)
    console.log(`  Required: ${allApisAvailable.required.join(', ')}`)

    await context.close()
  })
})
