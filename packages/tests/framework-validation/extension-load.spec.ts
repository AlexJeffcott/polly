import { test, expect, type BrowserContext } from '@playwright/test'
import path from 'node:path'
import { launchWithExtension, extensionPath } from './helpers/extension-helpers'

/**
 * Framework Validation: Extension Loading
 *
 * Tests that the extension loads correctly in Chrome and all
 * required files are present and valid.
 */

test.describe('Framework Validation: Extension Loading', () => {
  test.beforeAll(async ({ browserName }) => {
    // Only run on Chromium
    if (browserName !== 'chromium') {
      test.skip()
    }
  })

  test('extension loads successfully in Chrome', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    expect(extensionId).toBeTruthy()
    expect(extensionId).toMatch(/^[a-z]{32}$/) // Chrome extension IDs are 32 lowercase letters

    console.log(`✓ Extension loaded with ID: ${extensionId}`)

    await context.close()
  })

  test('background service worker is running', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const [background] = context.serviceWorkers()
    expect(background).toBeTruthy()
    if (!background) {
      throw new Error('Background service worker not found')
    }
    expect(background.url()).toContain(extensionId)
    expect(background.url()).toContain('background/index.js')

    console.log(`✓ Background service worker URL: ${background.url()}`)

    await context.close()
  })

  test('extension manifest is valid', async () => {
    const manifestPath = path.join(extensionPath, 'manifest.json')
    const manifest = await Bun.file(manifestPath).json()

    // Required manifest fields
    expect(manifest.manifest_version).toBe(3)
    expect(manifest.name).toBeTruthy()
    expect(manifest.version).toBeTruthy()
    expect(manifest.description).toBeTruthy()

    // Background service worker
    expect(manifest.background).toBeDefined()
    expect(manifest.background.service_worker).toBe('background/index.js')
    expect(manifest.background.type).toBe('module')

    // Permissions
    expect(Array.isArray(manifest.permissions)).toBe(true)
    expect(manifest.permissions).toContain('storage')
    expect(manifest.permissions).toContain('tabs')
    expect(manifest.permissions).toContain('scripting')
    expect(manifest.permissions).toContain('contextMenus')
    expect(manifest.permissions).toContain('offscreen')

    // Host permissions
    expect(Array.isArray(manifest.host_permissions)).toBe(true)
    expect(manifest.host_permissions.length).toBeGreaterThan(0)

    // Content scripts
    expect(Array.isArray(manifest.content_scripts)).toBe(true)
    expect(manifest.content_scripts[0].js).toContain('content/index.js')
    expect(manifest.content_scripts[0].css).toContain('content/styles.css')
    expect(manifest.content_scripts[0].run_at).toBe('document_idle')

    // Action (popup)
    expect(manifest.action).toBeDefined()
    expect(manifest.action.default_popup).toBe('popup/popup.html')

    // Options page
    expect(manifest.options_page).toBe('options/options.html')

    // DevTools
    expect(manifest.devtools_page).toBe('devtools/devtools.html')

    // Web accessible resources
    expect(Array.isArray(manifest.web_accessible_resources)).toBe(true)
    expect(manifest.web_accessible_resources[0].resources).toContain('page/index.js')

    console.log(`✓ Manifest is valid`)
  })

  test('all required files exist in dist', async () => {
    const requiredFiles = [
      'manifest.json',
      'background/index.js',
      'content/index.js',
      'content/styles.css',
      'page/index.js',
      'devtools/devtools.html',
      'devtools/panel.html',
      'devtools/index.js',
      'devtools/panel.js',
      'devtools/panel.css',
      'popup/popup.html',
      'popup/popup.js',
      'popup/popup.css',
      'options/options.html',
      'options/options.js',
      'options/options.css',
      'offscreen/offscreen.html',
      'offscreen/offscreen.js',
      'assets/icon16.png',
      'assets/icon48.png',
      'assets/icon128.png',
    ]

    for (const file of requiredFiles) {
      const filePath = path.join(extensionPath, file)
      const exists = await Bun.file(filePath).exists()
      expect(exists).toBe(true)
    }

    console.log(`✓ All ${requiredFiles.length} required files exist`)
  })

  test('compiled JavaScript has no build errors', async () => {
    const jsFiles = [
      'background/index.js',
      'content/index.js',
      'popup/popup.js',
      'options/options.js',
      'devtools/panel.js',
      'page/index.js',
      'offscreen/offscreen.js',
    ]

    for (const file of jsFiles) {
      const filePath = path.join(extensionPath, file)
      const content = await Bun.file(filePath).text()

      // Should not contain unprocessed template variables
      expect(content).not.toContain('process.env.')
      expect(content).not.toContain('${EXTENSION_NAME}')
      expect(content).not.toContain('${SUPPORTED_DOMAINS}')

      // Should have actual content
      expect(content.length).toBeGreaterThan(100)

      // Should not have obvious syntax errors
      expect(content).not.toContain('SyntaxError')
      expect(content).not.toContain('undefined is not')
    }

    console.log(`✓ All JavaScript files are valid`)
  })

  test('HTML files reference correct assets', async () => {
    const htmlFiles = [
      { file: 'popup/popup.html', js: 'popup.js', css: 'popup.css' },
      { file: 'options/options.html', js: 'options.js', css: 'options.css' },
      { file: 'devtools/panel.html', js: 'panel.js', css: 'panel.css' },
      { file: 'offscreen/offscreen.html', js: 'offscreen.js' },
    ]

    for (const { file, js, css } of htmlFiles) {
      const filePath = path.join(extensionPath, file)
      const content = await Bun.file(filePath).text()

      expect(content).toContain(js)
      if (css) {
        expect(content).toContain(css)
      }

      // Should not contain template variables
      expect(content).not.toContain('${EXTENSION_NAME}')
    }

    console.log(`✓ All HTML files are valid`)
  })

  test('popup page loads without errors', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const popupPage = await context.newPage()
    await popupPage.goto(`chrome-extension://${extensionId}/popup/popup.html`)
    await popupPage.waitForLoadState('domcontentloaded')

    // Check for console errors
    const errors: string[] = []
    popupPage.on('console', (msg) => {
      if (msg.type() === 'error') {
        errors.push(msg.text())
      }
    })

    await popupPage.waitForTimeout(1000) // Wait for any errors to appear

    expect(errors).toHaveLength(0)

    console.log(`✓ Popup page loads without errors`)

    await context.close()
  })

  test('options page loads without errors', async ({ playwright }) => {
    const { context, extensionId } = await launchWithExtension(playwright)

    const optionsPage = await context.newPage()
    await optionsPage.goto(`chrome-extension://${extensionId}/options/options.html`)
    await optionsPage.waitForLoadState('domcontentloaded')

    // Check for console errors
    const errors: string[] = []
    optionsPage.on('console', (msg) => {
      if (msg.type() === 'error') {
        errors.push(msg.text())
      }
    })

    await optionsPage.waitForTimeout(1000)

    expect(errors).toHaveLength(0)

    console.log(`✓ Options page loads without errors`)

    await context.close()
  })
})
