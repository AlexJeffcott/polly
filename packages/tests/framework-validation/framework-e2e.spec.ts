import { test, expect } from '@playwright/test'
import { launchWithExtension, openPopup } from './helpers/extension-helpers'

/**
 * Framework Validation: End-to-End Tests
 *
 * These tests use the instrumented extension approach:
 * 1. Extension runs framework code
 * 2. Framework dumps results to window.__TEST_RESULTS__
 * 3. Playwright validates the dumps
 *
 * This tests the ACTUAL framework behavior with REAL Chrome APIs
 */

interface TestResults {
  success: boolean
  context?: string
  errors?: unknown[]
  framework?: {
    messageBusInitialized: boolean
    adaptersAvailable: {
      runtime: boolean
      storage: boolean
      tabs: boolean
      window: boolean
      offscreen: boolean
      contextMenus: boolean
      fetch: boolean
      logger: boolean
    }
  }
  tests?: {
    messageRoundtrip?: {
      success: boolean
      processed: boolean
      context: string
      received?: {
        data: string
      }
    }
    storage?: {
      success: boolean
      matches: boolean
      written?: {
        testKey: string
      }
      retrieved?: string
    }
    tabs?: {
      success: boolean
      tabCount: number
      hasTabs: boolean
    }
    signalState?: {
      success: boolean
      hasSettings: boolean
      settingsValue?: unknown
      popupSignalValue?: unknown
    }
    logger?: {
      success: boolean
      loggerAvailable: boolean
    }
    runtime?: {
      success: boolean
      hasId: boolean
      extensionId?: string
    }
    aggregated?: {
      success: boolean
      allPassed: boolean
    }
    [key: string]: unknown
  }
}

function assertTestResults(results: unknown): asserts results is TestResults {
  if (!results || typeof results !== 'object') {
    throw new Error('Test results are not an object')
  }
}

test.describe('Framework Validation: End-to-End', () => {
  test.beforeAll(async ({ browserName }) => {
    if (browserName !== 'chromium') {
      test.skip()
    }
  })

  test('framework works end-to-end', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // Open popup with test mode enabled
    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    // Wait for tests to complete (check for window.__TEST_RESULTS__)
    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    // Get test results
    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    console.log('Framework test results:', JSON.stringify(results, null, 2))

    // Validate framework initialization
    expect(results).toBeTruthy()
    expect(results.success).toBe(true)
    expect(results.context).toBe('popup')
    expect(results.errors).toHaveLength(0)

    // Validate framework components are initialized
    expect(results.framework).toBeDefined()
    expect(results.framework!.messageBusInitialized).toBe(true)
    expect(results.framework!.adaptersAvailable.runtime).toBe(true)
    expect(results.framework!.adaptersAvailable.storage).toBe(true)
    expect(results.framework!.adaptersAvailable.tabs).toBe(true)
    expect(results.framework!.adaptersAvailable.window).toBe(true)
    expect(results.framework!.adaptersAvailable.offscreen).toBe(true)
    expect(results.framework!.adaptersAvailable.contextMenus).toBe(true)
    expect(results.framework!.adaptersAvailable.fetch).toBe(true)
    expect(results.framework!.adaptersAvailable.logger).toBe(true)

    console.log('✓ Framework initialized correctly')

    await context.close()
  })

  test('MessageBus cross-context messaging works', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Validate message round-trip (popup -> background -> popup)
    expect(results.tests).toBeDefined()
    expect(results.tests!.messageRoundtrip).toBeTruthy()
    expect(results.tests!.messageRoundtrip!.success).toBe(true)
    expect(results.tests!.messageRoundtrip!.processed).toBe(true)
    expect(results.tests!.messageRoundtrip!.context).toBe('background')
    expect(results.tests!.messageRoundtrip!.received!.data).toBe('test-from-popup')

    console.log('✓ MessageBus cross-context messaging works')
    console.log('  Popup -> Background -> Popup round-trip successful')

    await context.close()
  })

  test('StorageAdapter works', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Validate storage operations
    expect(results.tests).toBeDefined()
    expect(results.tests!.storage).toBeTruthy()
    expect(results.tests!.storage!.success).toBe(true)
    expect(results.tests!.storage!.matches).toBe(true)
    expect(results.tests!.storage!.written).toBeTruthy()
    expect(results.tests!.storage!.retrieved).toBe(results.tests!.storage!.written!.testKey)

    console.log('✓ StorageAdapter works')
    console.log(`  Wrote: ${results.tests!.storage!.written!.testKey}`)
    console.log(`  Retrieved: ${results.tests!.storage!.retrieved}`)

    await context.close()
  })

  test('TabsAdapter works', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Validate tabs operations
    expect(results.tests).toBeDefined()
    expect(results.tests!.tabs).toBeTruthy()
    expect(results.tests!.tabs!.success).toBe(true)
    expect(results.tests!.tabs!.hasTabs).toBe(true)
    expect(results.tests!.tabs!.tabCount).toBeGreaterThan(0)

    console.log('✓ TabsAdapter works')
    console.log(`  Found ${results.tests!.tabs!.tabCount} tabs`)

    await context.close()
  })

  test('Signal state synchronization works', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Validate signal state
    expect(results.tests).toBeDefined()
    expect(results.tests!.signalState).toBeTruthy()
    expect(results.tests!.signalState!.success).toBe(true)
    expect(results.tests!.signalState!.hasSettings).toBe(true)
    expect(results.tests!.signalState!.settingsValue).toBeTruthy()
    expect(results.tests!.signalState!.popupSignalValue).toBeTruthy()

    console.log('✓ Signal state synchronization works')
    console.log('  Background settings:', results.tests!.signalState!.settingsValue)
    console.log('  Popup settings:', results.tests!.signalState!.popupSignalValue)

    await context.close()
  })

  test('LoggerAdapter works', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Validate logger
    expect(results.tests).toBeDefined()
    expect(results.tests!.logger).toBeTruthy()
    expect(results.tests!.logger!.success).toBe(true)
    expect(results.tests!.logger!.loggerAvailable).toBe(true)

    console.log('✓ LoggerAdapter works')

    await context.close()
  })

  test('RuntimeAdapter works', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Validate runtime adapter
    expect(results.tests).toBeDefined()
    expect(results.tests!.runtime).toBeTruthy()
    expect(results.tests!.runtime!.success).toBe(true)
    expect(results.tests!.runtime!.hasId).toBe(true)
    expect(results.tests!.runtime!.extensionId).toBe(extensionId)

    console.log('✓ RuntimeAdapter works')
    console.log(`  Extension ID: ${results.tests!.runtime!.extensionId}`)

    await context.close()
  })

  test('all framework tests pass', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html?run-tests=true`)
    await popupPage.waitForLoadState('domcontentloaded')

    await popupPage.waitForFunction(
      () => window.__TEST_RESULTS__ !== undefined,
      { timeout: 10000 }
    )

    const results = await popupPage.evaluate(() => window.__TEST_RESULTS__)
    assertTestResults(results)

    // Check aggregated results from background
    expect(results.tests).toBeDefined()
    expect(results.tests!.aggregated).toBeTruthy()
    expect(results.tests!.aggregated!.success).toBe(true)
    expect(results.tests!.aggregated!.allPassed).toBe(true)

    // List all test results
    const testNames = Object.keys(results.tests!)
    console.log(`✓ All ${testNames.length} framework tests passed`)
    console.log('  Tests run:', testNames.join(', '))

    // Validate no errors occurred
    expect(results.errors).toHaveLength(0)
    expect(results.success).toBe(true)

    console.log('✓ Framework is production ready!')

    await context.close()
  })

  test('can run tests manually via window function', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    // Open popup WITHOUT auto-run
    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popupPage.waitForLoadState('domcontentloaded')

    // Manually run tests via exposed window function
    const results = await popupPage.evaluate(async () => {
      if (typeof window.__RUN_FRAMEWORK_TESTS__ === 'function') {
        return await window.__RUN_FRAMEWORK_TESTS__()
      }
      throw new Error('Test runner not found')
    })
    assertTestResults(results)

    expect(results).toBeTruthy()
    expect(results.success).toBe(true)

    console.log('✓ Manual test execution works')

    await context.close()
  })
})
