# Framework Validation Tests

This directory contains E2E tests that validate the Chrome extension framework itself works correctly in a real browser environment.

## Purpose

These tests are **not** for testing your specific extension features. They validate that the framework's core functionality works:

- ✅ Extension loads in Chrome
- ✅ All contexts (background, content, popup, devtools, options) initialize
- ✅ Cross-context messaging works
- ✅ State synchronization works
- ✅ Adapters work with real Chrome APIs
- ✅ Build output is correct

## Running Tests

```bash
# Build first
bun run build

# Run framework validation tests
bun playwright test tests/framework-validation

# Run with UI
bun playwright test tests/framework-validation --ui

# Debug specific test
bun playwright test tests/framework-validation/extension-load.spec.ts --debug
```

## Test Organization

```
tests/framework-validation/
├── README.md                    # This file
├── extension-load.spec.ts       # Extension loading & initialization
├── cross-context.spec.ts        # Cross-context messaging
├── state-sync.spec.ts           # State synchronization
├── adapters.spec.ts             # Adapter pattern validation
└── helpers/
    └── extension-helpers.ts     # Shared test utilities
```

## Prerequisites

- Extension must be built (`bun run build`)
- Tests run in headed mode (Chrome extensions don't work in headless)
- Chrome/Chromium must be installed

## Notes

- These tests use Playwright with real Chrome
- They load the extension from `dist/` directory
- They test the framework, not your application logic
- They ensure the framework is production-ready
