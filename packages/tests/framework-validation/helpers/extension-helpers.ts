import type { BrowserContext, Page } from '@playwright/test'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

export const extensionPath = path.resolve(__dirname, '../../../dist')

/**
 * Launch Chrome with the extension loaded
 */
export async function launchWithExtension(playwright: any): Promise<{
  context: BrowserContext
  extensionId: string
}> {
  const context = await playwright.chromium.launchPersistentContext('', {
    headless: false, // Extensions require headed mode
    args: [
      `--disable-extensions-except=${extensionPath}`,
      `--load-extension=${extensionPath}`,
      '--no-sandbox',
      '--disable-dev-shm-usage',
    ],
  })

  // Get extension ID from service worker
  let [background] = context.serviceWorkers()
  if (!background) {
    background = await context.waitForEvent('serviceworker')
  }

  const extensionIdMatch = background.url().match(/chrome-extension:\/\/([^\/]+)/)
  if (!extensionIdMatch) {
    throw new Error('Could not extract extension ID')
  }

  const extensionId = extensionIdMatch[1]
  return { context, extensionId }
}

/**
 * Navigate to extension popup
 */
export async function openPopup(
  context: BrowserContext,
  extensionId: string
): Promise<Page> {
  const popupPage = await context.newPage()
  await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html`)
  await popupPage.waitForLoadState('domcontentloaded')
  return popupPage
}

/**
 * Navigate to extension options page
 */
export async function openOptions(
  context: BrowserContext,
  extensionId: string
): Promise<Page> {
  const optionsPage = await context.newPage()
  await optionsPage.goto(`chrome-extension://${extensionId}/options/options.html`)
  await optionsPage.waitForLoadState('domcontentloaded')
  return optionsPage
}

/**
 * Navigate to a test page where content script should inject
 */
export async function navigateToTestPage(
  context: BrowserContext,
  url = 'https://example.com'
): Promise<Page> {
  const page = await context.newPage()
  await page.goto(url)
  await page.waitForLoadState('domcontentloaded')
  return page
}

/**
 * Wait for content script to be injected
 */
export async function waitForContentScript(page: Page, timeout = 5000): Promise<boolean> {
  try {
    await page.waitForFunction(
      () => {
        // Check if content script has injected a marker
        return document.documentElement.hasAttribute('data-extension-injected')
      },
      { timeout }
    )
    return true
  } catch {
    return false
  }
}

/**
 * Execute code in the extension's background service worker
 */
export async function evaluateInBackground<T>(
  context: BrowserContext,
  fn: () => T | Promise<T>
): Promise<T> {
  const [background] = context.serviceWorkers()
  if (!background) {
    throw new Error('Background service worker not found')
  }
  return background.evaluate(fn)
}

/**
 * Send a message from page to background and wait for response
 */
export async function sendMessageToBackground<T>(
  page: Page,
  message: unknown
): Promise<T> {
  return page.evaluate(async (msg) => {
    return new Promise((resolve, reject) => {
      // @ts-ignore - chrome is available in extension context
      chrome.runtime.sendMessage(msg, (response) => {
        // @ts-ignore
        if (chrome.runtime.lastError) {
          // @ts-ignore
          reject(chrome.runtime.lastError)
        } else {
          resolve(response)
        }
      })
    })
  }, message)
}

/**
 * Get chrome.storage.local data
 */
export async function getStorageData(
  context: BrowserContext,
  keys?: string | string[]
): Promise<Record<string, unknown>> {
  return evaluateInBackground<Record<string, unknown>>(context, () => {
    return new Promise((resolve) => {
      // @ts-ignore
      chrome.storage.local.get(keys, (result) => {
        resolve(result)
      })
    })
  })
}

/**
 * Set chrome.storage.local data
 */
export async function setStorageData(
  context: BrowserContext,
  data: Record<string, unknown>
): Promise<void> {
  return evaluateInBackground(context, () => {
    return new Promise<void>((resolve) => {
      // @ts-ignore
      chrome.storage.local.set(data, () => {
        resolve()
      })
    })
  })
}

/**
 * Clear chrome.storage.local
 */
export async function clearStorage(context: BrowserContext): Promise<void> {
  return evaluateInBackground(context, () => {
    return new Promise<void>((resolve) => {
      // @ts-ignore
      chrome.storage.local.clear(() => {
        resolve()
      })
    })
  })
}
