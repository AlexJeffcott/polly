import { test, expect, type BrowserContext } from '@playwright/test'
import path from 'node:path'

/**
 * Example E2E test for the example extension
 *
 * This demonstrates how to test Chrome extensions with Playwright.
 * The extension should be built before running tests.
 */

let context: BrowserContext

test.beforeAll(async ({ browserName }) => {
  const { chromium } = await import('playwright')

  // Path to built extension
  const extensionPath = path.join(process.cwd(), 'dist')

  // Launch browser with extension loaded
  context = await chromium.launchPersistentContext('', {
    headless: false,
    args: [
      `--disable-extensions-except=${extensionPath}`,
      `--load-extension=${extensionPath}`,
    ],
  })
})

test.afterAll(async () => {
  await context?.close()
})

test('extension loads successfully', async () => {
  // Get the extension's background page
  const backgroundPages = context.serviceWorkers()
  expect(backgroundPages.length).toBeGreaterThan(0)
})

test('popup displays test results', async () => {
  // Create a new page
  const page = await context.newPage()

  // Get extension ID
  const extensionId = context.serviceWorkers()[0]?.url().split('/')[2]

  // Navigate to popup
  await page.goto(`chrome-extension://${extensionId}/popup/popup.html`)

  // Wait for popup to load
  await page.waitForSelector('[data-testid="test-popup"]')

  // Check that context is displayed
  const contextText = await page.textContent('[data-testid="context"]')
  expect(contextText).toBe('popup')
})

test('background handlers respond correctly', async () => {
  const page = await context.newPage()
  const extensionId = context.serviceWorkers()[0]?.url().split('/')[2]

  await page.goto(`chrome-extension://${extensionId}/popup/popup.html`)
  await page.waitForSelector('[data-testid="run-all-tests"]')

  // Run all framework tests
  await page.click('[data-testid="run-all-tests"]')

  // Wait for tests to complete
  await page.waitForFunction(() => {
    const status = document.querySelector('[data-testid="test-status"]')
    return status?.textContent === 'success' || status?.textContent === 'error'
  }, { timeout: 5000 })

  // Check test status
  const status = await page.textContent('[data-testid="test-status"]')
  expect(status).toBe('success')
})

test('devtools panel loads', async () => {
  const page = await context.newPage()
  await page.goto('about:blank')

  const extensionId = context.serviceWorkers()[0]?.url().split('/')[2]

  // Open DevTools
  const client = await page.context().newCDPSession(page)

  // Navigate to devtools panel
  const devtoolsPage = await context.newPage()
  await devtoolsPage.goto(`chrome-extension://${extensionId}/devtools/test-devtools-panel.html`)

  // Check panel loads
  await devtoolsPage.waitForSelector('h2')
  const heading = await devtoolsPage.textContent('h2')
  expect(heading).toContain('Extension Framework Inspector')
})

test('options page loads and syncs state', async () => {
  const extensionId = context.serviceWorkers()[0]?.url().split('/')[2]

  const page = await context.newPage()
  await page.goto(`chrome-extension://${extensionId}/options/test-options.html`)

  // Wait for options page to load
  await page.waitForSelector('[data-testid="test-options"]')

  // Check context
  const optionsContext = await page.textContent('[data-testid="context"]')
  expect(optionsContext).toBe('options')
})

test('sidepanel loads', async () => {
  const extensionId = context.serviceWorkers()[0]?.url().split('/')[2]

  const page = await context.newPage()
  await page.goto(`chrome-extension://${extensionId}/sidepanel/test-sidepanel.html`)

  // Wait for sidepanel to load
  await page.waitForSelector('h1')
  const heading = await page.textContent('h1')
  expect(heading).toContain('Extension Side Panel')
})
