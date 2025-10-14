#!/usr/bin/env bun
/**
 * Build script for example extension
 *
 * This demonstrates how users would build their extension using the
 * framework's provided build tooling.
 *
 * Users can:
 * 1. Use the framework's build-user-extension.ts script directly
 * 2. Copy it to their project and customize
 * 3. Use their own build setup (Vite, Webpack, etc.)
 */

// Use the framework's build script
import '../../../scripts/build-user-extension.ts'

// The script will:
// - Clean dist/
// - Copy manifest.json
// - Copy HTML files
// - Copy assets
// - Build TypeScript files
// - Build CSS files
// - Handle path aliases (@/ imports)
