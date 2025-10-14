import { test, expect } from '@playwright/test'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const extensionPath = path.resolve(__dirname, 'test-extension/dist')

async function launchWithExtension(playwright: any) {
  const context = await playwright.chromium.launchPersistentContext('', {
    headless: false,
    args: [
      `--disable-extensions-except=${extensionPath}`,
      `--load-extension=${extensionPath}`,
      '--no-sandbox',
    ],
  })

  let [background] = context.serviceWorkers()
  if (!background) {
    background = await context.waitForEvent('serviceworker')
  }

  const extensionIdMatch = background.url().match(/chrome-extension:\/\/([^\/]+)/)
  if (!extensionIdMatch) {
    throw new Error('Could not extract extension ID')
  }

  return { context, extensionId: extensionIdMatch[1] }
}

test.describe('Simple State Tests', () => {
  test.beforeAll(async ({ browserName }) => {
    if (browserName !== 'chromium') {
      test.skip()
    }
  })

  test('$sharedState syncs from popup to options', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // Open popup
    const popup = await context.newPage()
    popup.on('console', (msg) => console.log('POPUP:', msg.text()))
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Open options
    const options = await context.newPage()
    options.on('console', (msg) => console.log('OPTIONS:', msg.text()))
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    // Wait for contexts to connect
    await popup.waitForTimeout(500)

    // Both should start at 0
    const popupInitial = await popup.locator('[data-testid="simple-shared-value"]').textContent()
    const optionsInitial = await options.locator('[data-testid="options-simple-shared-value"]').textContent()

    console.log('Initial - Popup:', popupInitial, 'Options:', optionsInitial)
    expect(popupInitial).toBe('0')
    expect(optionsInitial).toBe('0')

    // Click increment in popup
    await popup.click('[data-testid="simple-shared-increment"]')

    console.log('Clicked increment, waiting...')
    await popup.waitForTimeout(1000)

    // Read values
    const popupValue = await popup.locator('[data-testid="simple-shared-value"]').textContent()
    const optionsValue = await options.locator('[data-testid="options-simple-shared-value"]').textContent()

    console.log('After increment - Popup:', popupValue, 'Options:', optionsValue)

    // Popup should definitely be 1
    expect(popupValue).toBe('1')

    // Options should ALSO be 1 (this is what we're testing!)
    expect(optionsValue).toBe('1')

    console.log('✓✓✓ $sharedState SYNC WORKS! ✓✓✓')

    await context.close()
  })

  test('$syncedState syncs from popup to options', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    const options = await context.newPage()
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    await popup.waitForTimeout(500)

    // Both start at 0
    expect(await popup.locator('[data-testid="simple-synced-value"]').textContent()).toBe('0')
    expect(await options.locator('[data-testid="options-simple-synced-value"]').textContent()).toBe('0')

    // Click increment
    await popup.click('[data-testid="simple-synced-increment"]')
    await popup.waitForTimeout(1000)

    // Read values
    const popupValue = await popup.locator('[data-testid="simple-synced-value"]').textContent()
    const optionsValue = await options.locator('[data-testid="options-simple-synced-value"]').textContent()

    console.log('After increment - Popup:', popupValue, 'Options:', optionsValue)

    expect(popupValue).toBe('1')
    expect(optionsValue).toBe('1')

    console.log('✓✓✓ $syncedState SYNC WORKS! ✓✓✓')

    await context.close()
  })
})
