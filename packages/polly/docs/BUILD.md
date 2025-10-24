# Build System

## Overview

The build system uses **Bun** as the build tool and runtime. It provides:

- **Environment variable injection** from `.env` files
- **Manifest template processing** with variable substitution
- **Multi-context bundling** for all extension contexts
- **CSS modules** support
- **Watch mode** for development
- **Production optimization** (minification, no source maps)
- **Build-time constants** via `define`

## Quick Start

```bash
# Development build (with source maps)
bun run build

# Production build (minified, optimized)
bun run build:prod

# Watch mode (auto-rebuild on changes)
bun run dev

# Type checking
bun run typecheck

# Linting
bun run lint:fix
```

## Environment Variables

### Configuration File

Create a `.env` file in the project root:

```bash
# .env
SUPPORTED_DOMAINS=https://localhost:2222/*,https://example.com/*
EXTENSION_NAME=My Chrome Extension
RELEASE_SPACE_URL=https://github.com/user/repo/releases
FEEDBACK_SPACE_URL=https://github.com/user/repo/issues
```

### Available Variables

| Variable | Description | Default | Used In |
|----------|-------------|---------|---------|
| `SUPPORTED_DOMAINS` | Comma-separated list of URL patterns | `https://localhost:2222/*` | Manifest, code |
| `EXTENSION_NAME` | Extension display name | `Chrome Extension` | Manifest, code |
| `RELEASE_SPACE_URL` | URL for release notes | `""` | Code |
| `FEEDBACK_SPACE_URL` | URL for feedback/issues | `""` | Code |
| `VERSION` | Extension version | From `package.json` | Manifest, code |
| `BUILD_TIMESTAMP` | ISO timestamp of build | Auto-generated | Code |
| `NODE_ENV` | Environment mode | `production` or `development` | Code |

### How Variables Are Injected

#### 1. Manifest Template Processing

The `src/manifest.json` file can use template variables:

```json
{
  "name": "${EXTENSION_NAME}",
  "version": "1.0.0",
  "host_permissions": ["${SUPPORTED_DOMAINS}"],
  "content_scripts": [{
    "matches": ["${SUPPORTED_DOMAINS}"],
    "js": ["content.js"]
  }]
}
```

At build time, these are replaced:

```json
{
  "name": "My Chrome Extension",
  "version": "0.1.0",
  "host_permissions": [
    "https://localhost:2222/*",
    "https://example.com/*"
  ],
  "content_scripts": [{
    "matches": [
      "https://localhost:2222/*",
      "https://example.com/*"
    ],
    "js": ["content.js"]
  }]
}
```

#### 2. TypeScript Code Injection

Use `process.env` in your TypeScript code:

```typescript
// src/background/index.ts
console.log('Extension name:', process.env.EXTENSION_NAME)
console.log('Version:', process.env.VERSION)
console.log('Build timestamp:', process.env.BUILD_TIMESTAMP)

if (process.env.NODE_ENV === 'development') {
  console.log('Running in development mode')
}
```

At build time, these are replaced with literal values:

```typescript
// dist/background/index.js
console.log('Extension name:', "My Chrome Extension")
console.log('Version:', "0.1.0")
console.log('Build timestamp:', "2024-10-01T12:34:56.789Z")

if ("development" === 'development') {
  console.log('Running in development mode')
}
```

#### 3. HTML Template Variables

HTML files can also use template variables:

```html
<!-- src/popup/popup.html -->
<!DOCTYPE html>
<html>
<head>
  <title>${EXTENSION_NAME}</title>
  <meta name="version" content="${VERSION}">
</head>
<body>
  <h1>${EXTENSION_NAME}</h1>
  <p>Built: ${BUILD_TIMESTAMP}</p>
</body>
</html>
```

These are replaced at build time.

## Managing Permissions via Environment Variables

### Host Permissions Pattern

The `SUPPORTED_DOMAINS` variable is the primary way to configure which sites your extension can access.

#### Single Domain
```bash
SUPPORTED_DOMAINS=https://example.com/*
```

#### Multiple Domains (Comma-Separated)
```bash
SUPPORTED_DOMAINS=https://example.com/*,https://api.example.com/*,https://cdn.example.com/*
```

#### Wildcard Subdomains
```bash
SUPPORTED_DOMAINS=https://*.example.com/*
```

#### Development + Production Domains
```bash
SUPPORTED_DOMAINS=https://localhost:3000/*,https://staging.example.com/*,https://example.com/*
```

#### All URLs (Use with Caution)
```bash
SUPPORTED_DOMAINS=<all_urls>
```

### Manifest Template System

The build system automatically expands `${SUPPORTED_DOMAINS}` in all relevant manifest fields:

```json
{
  "host_permissions": ["${SUPPORTED_DOMAINS}"],

  "content_scripts": [{
    "matches": ["${SUPPORTED_DOMAINS}"],
    "js": ["content.js"]
  }],

  "web_accessible_resources": [{
    "resources": ["page.js"],
    "matches": ["${SUPPORTED_DOMAINS}"]
  }]
}
```

**All three fields** will be expanded to the array of domains from your `.env` file.

### Advanced Permission Patterns

#### Mixing Template Variables with Static Permissions

You can combine environment variables with static permissions:

```json
{
  "host_permissions": [
    "${SUPPORTED_DOMAINS}",
    "https://fonts.googleapis.com/*",
    "https://cdn.jsdelivr.net/*"
  ]
}
```

Result:
```json
{
  "host_permissions": [
    "https://example.com/*",
    "https://api.example.com/*",
    "https://fonts.googleapis.com/*",
    "https://cdn.jsdelivr.net/*"
  ]
}
```

#### Content Script Matching Specific Domains

If you want different content scripts for different domains, you can't use the template directly. Instead:

**Option 1**: Use separate manifest entries
```json
{
  "content_scripts": [
    {
      "matches": ["${SUPPORTED_DOMAINS}"],
      "js": ["content.js"],
      "run_at": "document_idle"
    },
    {
      "matches": ["https://special-domain.com/*"],
      "js": ["content.js", "special-handler.js"],
      "run_at": "document_start"
    }
  ]
}
```

**Option 2**: Use runtime configuration in code
```typescript
// src/content/index.ts
const hostname = window.location.hostname

if (hostname === 'special-domain.com') {
  // Special handling for this domain
  import('./special-handler')
}
```

### Adding New Environment Variables

To add a new environment variable:

#### 1. Add to `.env` file
```bash
MY_API_KEY=abc123
```

#### 2. Add to build script env object
```typescript
// build.ts
const env = {
  SUPPORTED_DOMAINS: envVars.SUPPORTED_DOMAINS || '...',
  EXTENSION_NAME: envVars.EXTENSION_NAME || '...',
  MY_API_KEY: envVars.MY_API_KEY || process.env.MY_API_KEY || '', // Add this
  // ...
}
```

#### 3. Add to define object (for code injection)
```typescript
// build.ts - in buildTypeScript()
define: {
  'process.env.SUPPORTED_DOMAINS': JSON.stringify(env.SUPPORTED_DOMAINS),
  'process.env.EXTENSION_NAME': JSON.stringify(env.EXTENSION_NAME),
  'process.env.MY_API_KEY': JSON.stringify(env.MY_API_KEY), // Add this
  // ...
}
```

#### 4. Use in your code
```typescript
// src/background/api-client.ts
const API_KEY = process.env.MY_API_KEY

fetch(`https://api.example.com/data?key=${API_KEY}`)
```

### Sensitive Variables

**⚠️ Important**: Never commit sensitive data to `.env` files in public repositories.

**Best practices**:

1. **Use `.env.example` for templates**:
   ```bash
   # .env.example (committed)
   SUPPORTED_DOMAINS=https://example.com/*
   EXTENSION_NAME=My Extension
   MY_API_KEY=your_api_key_here
   ```

2. **Keep `.env` in `.gitignore`**:
   ```gitignore
   # .gitignore
   .env
   .env.local
   ```

3. **For secrets, use alternative approaches**:
   - Prompt user to enter API keys in Options page
   - Store secrets in `chrome.storage` (user-specific)
   - Use OAuth flows instead of hardcoded keys

4. **For team development**:
   - Share `.env` via secure channels (1Password, etc.)
   - Or use separate team members' API keys

## Build Configuration

### Entry Points

All entry points are defined in `build.ts`:

```typescript
const entryPoints: EntryPoint[] = [
  // Background service worker
  { in: 'src/background/index.ts', out: 'background/index.js', type: 'ts' },

  // Content script
  { in: 'src/content/index.ts', out: 'content/index.js', type: 'ts' },
  { in: 'src/content/styles.module.css', out: 'content/styles.css', type: 'css' },

  // Page script
  { in: 'src/page/index.ts', out: 'page/index.js', type: 'ts' },

  // DevTools
  { in: 'src/devtools/index.ts', out: 'devtools/index.js', type: 'ts' },
  { in: 'src/devtools/panel.tsx', out: 'devtools/panel.js', type: 'tsx' },
  { in: 'src/devtools/panel.module.css', out: 'devtools/panel.css', type: 'css' },
  { in: 'src/devtools/devtools.html', out: 'devtools/devtools.html', type: 'html' },
  { in: 'src/devtools/panel.html', out: 'devtools/panel.html', type: 'html' },

  // Popup
  { in: 'src/popup/index.tsx', out: 'popup/popup.js', type: 'tsx' },
  { in: 'src/popup/popup.module.css', out: 'popup/popup.css', type: 'css' },
  { in: 'src/popup/popup.html', out: 'popup/popup.html', type: 'html' },

  // Options
  { in: 'src/options/index.tsx', out: 'options/options.js', type: 'tsx' },
  { in: 'src/options/options.module.css', out: 'options/options.css', type: 'css' },
  { in: 'src/options/options.html', out: 'options/options.html', type: 'html' },

  // Offscreen
  { in: 'src/offscreen/index.ts', out: 'offscreen/offscreen.js', type: 'ts' },
  { in: 'src/offscreen/offscreen.html', out: 'offscreen/offscreen.html', type: 'html' },

  // Assets
  { in: 'src/assets/icon16.png', out: 'assets/icon16.png', type: 'asset' },
  { in: 'src/assets/icon48.png', out: 'assets/icon48.png', type: 'asset' },
  { in: 'src/assets/icon128.png', out: 'assets/icon128.png', type: 'asset' },
]
```

### Adding New Entry Points

To add a new context or file, add an entry to the `entryPoints` array:

```typescript
// Add a new context (e.g., sidebar)
{ in: 'src/sidebar/index.tsx', out: 'sidebar/sidebar.js', type: 'tsx' },
{ in: 'src/sidebar/sidebar.html', out: 'sidebar/sidebar.html', type: 'html' },
{ in: 'src/sidebar/sidebar.module.css', out: 'sidebar/sidebar.css', type: 'css' },
```

### Bun.build Configuration

TypeScript/TSX files are built with:

```typescript
await Bun.build({
  entrypoints: tsEntries.map((e) => e.in),
  outdir: 'dist',
  format: 'esm',                    // ES modules
  target: 'browser',                 // Browser environment
  minify: isProd,                    // Minify in production
  sourcemap: isProd ? 'none' : 'inline', // Source maps in dev only
  splitting: false,                  // No code splitting (Chrome limitation)
  external: ['chrome'],              // Don't bundle chrome APIs
  define: {
    // Replace process.env at build time
    'process.env.EXTENSION_NAME': JSON.stringify(env.EXTENSION_NAME),
    'process.env.VERSION': JSON.stringify(env.VERSION),
    // ... etc
  },
})
```

## Output Structure

```
dist/
├── manifest.json              # Processed manifest
├── background/
│   └── index.js              # Background service worker
├── content/
│   ├── index.js              # Content script
│   └── styles.css            # Content script styles
├── page/
│   └── index.js              # Page script (injected)
├── devtools/
│   ├── index.js              # DevTools registration
│   ├── panel.js              # DevTools panel UI
│   ├── panel.css             # Panel styles
│   ├── devtools.html         # DevTools entry point
│   └── panel.html            # Panel HTML
├── popup/
│   ├── popup.js              # Popup UI
│   ├── popup.css             # Popup styles
│   └── popup.html            # Popup HTML
├── options/
│   ├── options.js            # Options UI
│   ├── options.css           # Options styles
│   └── options.html          # Options HTML
├── offscreen/
│   ├── offscreen.js          # Offscreen document script
│   └── offscreen.html        # Offscreen HTML
└── assets/
    ├── icon16.png
    ├── icon48.png
    └── icon128.png
```

## Build Process

The build happens in 6 steps:

### 1. Clean

```typescript
rmSync('dist', { recursive: true, force: true })
mkdirSync('dist', { recursive: true })
```

Removes previous build artifacts.

### 2. Process Manifest

- Read `src/manifest.json`
- Replace `${EXTENSION_NAME}` with actual name
- Replace `${VERSION}` with package.json version
- Expand `${SUPPORTED_DOMAINS}` into array of domains
- Add CSP in development mode
- Write to `dist/manifest.json`

### 3. Copy HTML Files

- Read HTML files from `src/**/*.html`
- Replace template variables (`${EXTENSION_NAME}`, etc.)
- Write to `dist/` with correct paths

### 4. Copy Assets

- Copy binary assets (images, fonts, etc.)
- Preserve directory structure

### 5. Build CSS

- Process CSS/CSS Modules
- Minify in production
- Write to `dist/` with correct paths

### 6. Build TypeScript/TSX

- Bundle all `.ts` and `.tsx` files
- Inject environment variables via `define`
- Transform JSX (Preact)
- Minify in production
- Generate source maps in development
- Write to `dist/` with correct paths

## Development Workflow

### Watch Mode

```bash
bun run dev
```

This:
1. Performs initial build
2. Watches `src/` directory for changes
3. Rebuilds automatically on file changes
4. Prevents concurrent builds (queues if already building)

### Loading Extension

1. Open Chrome: `chrome://extensions`
2. Enable "Developer mode"
3. Click "Load unpacked"
4. Select the `dist/` folder
5. Extension loads!

### Hot Reload

After rebuilding:
1. Click the reload icon on the extension card in `chrome://extensions`
2. Or use a keyboard shortcut (if configured)

**Note**: Some changes require full extension reload:
- Manifest changes
- Background script changes
- Permission changes

Content script and UI changes usually only require page reload.

## Production Build

```bash
bun run build:prod
```

Differences from development build:

| Feature | Development | Production |
|---------|-------------|------------|
| Minification | ❌ No | ✅ Yes |
| Source maps | ✅ Inline | ❌ None |
| CSP in manifest | ✅ Added | ❌ Not added |
| `NODE_ENV` | `development` | `production` |
| Build time | ~500ms | ~800ms |
| Output size | ~200KB | ~80KB |

### Distribution

```bash
# Build for production
bun run build:prod

# Create zip for Chrome Web Store
cd dist
zip -r ../extension-v0.1.0.zip .
cd ..

# Upload extension-v0.1.0.zip to Chrome Web Store
```

## Troubleshooting

### "Asset not found (skipping)"

**Cause**: Entry point in `build.ts` references a file that doesn't exist.

**Solution**:
- Create the file, or
- Remove the entry from `entryPoints` array

### "TypeScript build failed"

**Cause**: TypeScript compilation error.

**Solution**:
```bash
# Check types
bun run typecheck

# See detailed errors
```

### "No TypeScript files found to build"

**Cause**: None of the entry points exist yet.

**Solution**: Create at least one entry point file (e.g., `src/background/index.ts`).

### Manifest not updating

**Cause**: Cached manifest in Chrome.

**Solution**:
1. Go to `chrome://extensions`
2. Click reload button on extension card
3. Or remove and re-add extension

### Environment variables not working

**Cause**:
- `.env` file syntax error
- Variable not added to `define` in `build.ts`

**Solution**:
1. Check `.env` syntax (no spaces around `=`)
2. Add variable to `define` object in `buildTypeScript()`:
   ```typescript
   define: {
     'process.env.MY_VAR': JSON.stringify(env.MY_VAR),
   }
   ```

### Host permissions not applying

**Cause**: The domain pattern might be incorrect.

**Solution**:
1. Check Chrome's [match pattern documentation](https://developer.chrome.com/docs/extensions/mv3/match_patterns/)
2. Valid patterns:
   - `https://example.com/*` (specific subdomain)
   - `https://*.example.com/*` (all subdomains)
   - `*://example.com/*` (http and https)
   - `<all_urls>` (all URLs - requires justification)
3. Invalid patterns:
   - `https://example.com` (missing path)
   - `example.com/*` (missing scheme)

## Performance

Build times on Apple M1 Pro:

| Build Type | Time | Output Size |
|------------|------|-------------|
| Development (cold) | ~600ms | ~250KB |
| Development (warm) | ~200ms | ~250KB |
| Production | ~900ms | ~90KB |
| Watch rebuild | ~150ms | varies |

Tips for faster builds:
- Use watch mode during development (incremental builds)
- Only build contexts you're actively working on (comment out unused entries)
- Use `--prod` only when testing final build

## Advanced

### Custom Build Steps

Add custom processing between steps:

```typescript
async function build() {
  await cleanDist()
  await processManifest()
  await copyHTMLFiles()

  // Add custom step here
  await generateIcons() // Your custom function

  await copyAssets()
  await buildCSS()
  await buildTypeScript()
}
```

### Conditional Entry Points

Build different files based on environment:

```typescript
const entryPoints: EntryPoint[] = [
  { in: 'src/background/index.ts', out: 'background/index.js', type: 'ts' },

  // Only include analytics in production
  ...(isProd ? [
    { in: 'src/shared/analytics.ts', out: 'shared/analytics.js', type: 'ts' }
  ] : []),
]
```

### Post-Build Validation

Add validation after build:

```typescript
async function validateBuild() {
  // Check manifest exists
  if (!existsSync('dist/manifest.json')) {
    throw new Error('Manifest not found!')
  }

  // Check required files
  const required = ['background/index.js', 'content/index.js']
  for (const file of required) {
    if (!existsSync(`dist/${file}`)) {
      throw new Error(`Required file missing: ${file}`)
    }
  }

  console.log('✅ Build validation passed')
}

async function build() {
  // ... build steps ...
  await validateBuild()
}
```

## See Also

- [ARCHITECTURE.md](./ARCHITECTURE.md) - Overall architecture
- [TECHNICAL.md](./TECHNICAL.md) - Implementation details
- [Bun Build API](https://bun.sh/docs/bundler)
- [Chrome Extension Match Patterns](https://developer.chrome.com/docs/extensions/mv3/match_patterns/)
