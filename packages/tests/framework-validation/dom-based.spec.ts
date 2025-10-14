import { test, expect, type BrowserContext, type Page } from '@playwright/test'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

// Point to the test extension build output
// (Test extension imports from framework via path aliases)
const extensionPath = path.resolve(__dirname, 'test-extension/dist')

/**
 * Framework Validation: DOM-Based Testing
 *
 * Tests the framework by:
 * 1. Rendering state to DOM via test UI
 * 2. Interacting with DOM (clicks, inputs)
 * 3. Watching DOM update automatically (reactivity)
 * 4. Testing cross-context synchronization
 * 5. Testing persistence
 */

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

test.describe('Framework Validation: DOM-Based Testing', () => {
  test.beforeAll(async ({ browserName }) => {
    if (browserName !== 'chromium') {
      test.skip()
    }
  })

  test('extension loads and initializes', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    expect(extensionId).toBeTruthy()
    expect(extensionId).toMatch(/^[a-z]{32}$/)

    console.log(`✓ Extension loaded: ${extensionId}`)

    await context.close()
  })

  test('popup renders with test UI', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // Open popup
    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Check test popup is rendered
    const testPopup = await popup.locator('[data-testid="test-popup"]')
    expect(await testPopup.isVisible()).toBe(true)

    console.log('✓ Test popup UI rendered')

    await context.close()
  })

  test('$sharedState reactivity - counter increments', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Read initial counter value
    const initialValue = await popup.locator('[data-testid="test-counter"]').textContent()
    expect(initialValue).toBe('0')

    // Click increment button
    await popup.click('[data-testid="increment-counter"]')

    // Wait for DOM to update (should be immediate due to signals)
    await popup.waitForTimeout(100)

    // Counter should be 1
    const newValue = await popup.locator('[data-testid="test-counter"]').textContent()
    expect(newValue).toBe('1')

    console.log('✓ Counter incremented: 0 → 1')

    // Click again
    await popup.click('[data-testid="increment-counter"]')
    await popup.waitForTimeout(100)

    expect(await popup.locator('[data-testid="test-counter"]').textContent()).toBe('2')

    console.log('✓ Counter incremented: 1 → 2')

    await context.close()
  })

  test('$sharedState reactivity - color select', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Initial color
    const initialColor = await popup.locator('[data-testid="test-color"]').textContent()
    expect(initialColor).toBe('blue')

    // Change color
    await popup.selectOption('[data-testid="select-color"]', 'red')
    await popup.waitForTimeout(100)

    // Color should update
    const newColor = await popup.locator('[data-testid="test-color"]').textContent()
    expect(newColor).toBe('red')

    console.log('✓ Color changed: blue → red')

    await context.close()
  })

  test('$syncedState reactivity - message input', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Initial message is empty
    const initialMessage = await popup.locator('[data-testid="test-message"]').textContent()
    expect(initialMessage).toBe('')

    // Type in input
    await popup.fill('[data-testid="input-message"]', 'Hello Framework!')
    await popup.waitForTimeout(100)

    // Message should update
    const newMessage = await popup.locator('[data-testid="test-message"]').textContent()
    expect(newMessage).toBe('Hello Framework!')

    console.log('✓ Message updated: "" → "Hello Framework!"')

    await context.close()
  })

  test('local signal is NOT synced', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Increment local counter
    await popup.click('[data-testid="increment-local"]')
    await popup.waitForTimeout(100)

    const popupLocal = await popup.locator('[data-testid="local-counter"]').textContent()
    expect(popupLocal).toBe('1')

    console.log('✓ Local counter in popup: 1')

    await context.close()
  })

  test('CROSS-CONTEXT SYNC: $sharedState syncs popup → options', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // Open both popup and options
    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    const options = await context.newPage()
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    // Verify both show same initial value
    const popupCounter = await popup.locator('[data-testid="test-counter"]').textContent()
    const optionsCounter = await options.locator('[data-testid="options-counter"]').textContent()

    expect(popupCounter).toBe(optionsCounter)

    console.log(`✓ Initial sync - both show: ${popupCounter}`)

    // Increment in popup
    await popup.click('[data-testid="increment-counter"]')
    await popup.waitForTimeout(1000) // Give time for sync

    // Read values
    const newPopupValue = await popup.locator('[data-testid="test-counter"]').textContent()
    const newOptionsValue = await options.locator('[data-testid="options-counter"]').textContent()

    // Both should be updated!
    expect(newPopupValue).toBe('1')
    expect(newOptionsValue).toBe('1')

    console.log('✓ CROSS-CONTEXT SYNC WORKS!')
    console.log(`  Popup: ${newPopupValue}`)
    console.log(`  Options: ${newOptionsValue}`)

    await context.close()
  })

  test('CROSS-CONTEXT SYNC: $sharedState syncs options → popup', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    const options = await context.newPage()
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    // Increment in OPTIONS this time
    await options.click('[data-testid="options-increment"]')
    await options.waitForTimeout(200)

    // Both should update
    const popupValue = await popup.locator('[data-testid="test-counter"]').textContent()
    const optionsValue = await options.locator('[data-testid="options-counter"]').textContent()

    expect(popupValue).toBe('1')
    expect(optionsValue).toBe('1')

    console.log('✓ Reverse sync works (options → popup)!')

    await context.close()
  })

  test('CROSS-CONTEXT SYNC: $syncedState syncs popup → options', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    const options = await context.newPage()
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    // Type message in popup
    await popup.fill('[data-testid="input-message"]', 'Test sync!')
    await popup.waitForTimeout(200)

    // Options should show same message
    const popupMessage = await popup.locator('[data-testid="test-message"]').textContent()
    const optionsMessage = await options.locator('[data-testid="options-message"]').textContent()

    expect(popupMessage).toBe('Test sync!')
    expect(optionsMessage).toBe('Test sync!')

    console.log('✓ $syncedState cross-context sync works!')

    await context.close()
  })

  test('LOCAL SIGNAL: does NOT sync across contexts', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    const options = await context.newPage()
    await options.goto(`chrome-extension://${extensionId}/options/options.html`)
    await options.waitForLoadState('domcontentloaded')

    // Increment local in popup
    await popup.click('[data-testid="increment-local"]')
    await popup.click('[data-testid="increment-local"]')
    await popup.waitForTimeout(200)

    // Increment local in options
    await options.click('[data-testid="options-increment-local"]')
    await options.waitForTimeout(200)

    // Should be different!
    const popupLocal = await popup.locator('[data-testid="local-counter"]').textContent()
    const optionsLocal = await options.locator('[data-testid="options-local-counter"]').textContent()

    expect(popupLocal).toBe('2')
    expect(optionsLocal).toBe('1')

    console.log('✓ Local signals are independent:')
    console.log(`  Popup: ${popupLocal}`)
    console.log(`  Options: ${optionsLocal}`)

    await context.close()
  })

  test('PERSISTENCE: $sharedState persists after reload', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // First session: set counter to 5
    let popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Click 5 times
    for (let i = 0; i < 5; i++) {
      await popup.click('[data-testid="increment-counter"]')
      await popup.waitForTimeout(50)
    }

    const valueBeforeClose = await popup.locator('[data-testid="test-counter"]').textContent()
    expect(valueBeforeClose).toBe('5')

    console.log('✓ Counter set to 5')

    // Close popup
    await popup.close()

    // Wait for storage sync
    await new Promise(resolve => setTimeout(resolve, 500))

    // Reopen popup
    popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')
    await popup.waitForTimeout(200)

    // Should still be 5!
    const valueAfterReopen = await popup.locator('[data-testid="test-counter"]').textContent()
    expect(valueAfterReopen).toBe('5')

    console.log('✓ PERSISTENCE WORKS! Counter still shows 5 after reload')

    await context.close()
  })

  test('MessageBus: storage test via button', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Click storage test button
    await popup.click('[data-testid="run-storage-test"]')

    // Wait for test to complete
    await popup.waitForTimeout(1000)

    // Check status
    const status = await popup.locator('[data-testid="test-status"]').textContent()
    expect(status).toBe('success')

    // Check result
    const resultText = await popup.locator('[data-testid="test-results-json"]').textContent()
    const result = JSON.parse(resultText)

    expect(result.storage).toBeDefined()
    expect(result.storage.success).toBe(true)

    console.log('✓ Storage test passed via MessageBus')

    await context.close()
  })

  test('MessageBus: tabs test via button', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popup = await context.newPage()
    await popup.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popup.waitForLoadState('domcontentloaded')

    // Click tabs test button
    await popup.click('[data-testid="run-tabs-test"]')
    await popup.waitForTimeout(1000)

    // Check result
    const resultText = await popup.locator('[data-testid="test-results-json"]').textContent()
    const result = JSON.parse(resultText)

    expect(result.tabs).toBeDefined()
    expect(result.tabs.success).toBe(true)
    expect(result.tabs.tabCount).toBeGreaterThan(0)

    console.log(`✓ Tabs test passed - found ${result.tabs.tabCount} tabs`)

    await context.close()
  })

})
