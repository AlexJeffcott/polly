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

test.describe('Simple Broadcast Test', () => {
  test.beforeAll(async ({ browserName }) => {
    if (browserName !== 'chromium') {
      test.skip()
    }
  })

  test('popup can broadcast message to options', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // Open popup
    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Open options
    const options = await context.newPage()
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    // Wait a bit for contexts to connect
    await popup.waitForTimeout(500)

    // Initial state
    const initialOptionsStatus = await options.locator('[data-testid="ping-received"]').textContent()
    expect(initialOptionsStatus).toBe('No pings received')

    console.log('✓ Initial state: no pings received')

    // Check button exists
    const button = popup.locator('[data-testid="send-ping"]')
    const buttonExists = await button.count()
    console.log('Button exists:', buttonExists)

    if (buttonExists === 0) {
      throw new Error('Send ping button not found!')
    }

    // Send ping from popup
    await button.click()

    console.log('✓ Clicked send ping button')

    // Wait for broadcast
    await popup.waitForTimeout(1000)

    // Check options received the ping
    const optionsStatus = await options.locator('[data-testid="ping-received"]').textContent()
    console.log('Options status:', optionsStatus)
    expect(optionsStatus).toContain('Received ping at')

    // Check popup received the pong back
    const popupStatus = await popup.locator('[data-testid="ping-status"]').textContent()
    console.log('Popup status:', popupStatus)
    expect(popupStatus).toContain('Received pong at')

    console.log('✓✓✓ BROADCAST WORKS! popup → options → popup ✓✓✓')

    await context.close()
  })
})
