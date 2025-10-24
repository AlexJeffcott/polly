#!/usr/bin/env bun
// Build script for the visualize library

import { $ } from "bun"

console.log("Building @fairfox/web-ext-visualize...")

// Clean dist
await $`rm -rf dist`

// Build with TypeScript compiler
await $`bunx tsc --project tsconfig.json`

console.log("✓ Build complete")
