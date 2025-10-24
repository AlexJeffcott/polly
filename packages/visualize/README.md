# @fairfox/web-ext-visualize

Automatic architecture documentation for web extensions using Structurizr and the C4 model.

## Overview

Analyzes your Chrome extension codebase and automatically generates:
- **System Context diagrams** - Your extension and its external dependencies
- **Container diagrams** - Extension contexts (background, content, popup, etc.)
- **Component diagrams** - Internal structure of contexts
- **Dynamic diagrams** - Message flows between contexts

All from your TypeScript code with zero manual effort.

## Installation

```bash
# Using Bun (recommended)
bun add -D @fairfox/web-ext-visualize

# Using npm
npm install --save-dev @fairfox/web-ext-visualize

# Using pnpm
pnpm add -D @fairfox/web-ext-visualize
```

## Quick Start

```bash
# Generate architecture documentation
bunx web-ext-visualize

# View with Structurizr Lite
cd docs
docker run -it --rm -p 8080:8080 \
  -v $(pwd):/usr/local/structurizr \
  structurizr/lite

# Open http://localhost:8080
```

## What It Generates

### 1. System Context Diagram

Shows your extension in relation to:
- Users
- External APIs (REST, GraphQL, WebSocket)
- Browser APIs
- External services

### 2. Container Diagram

Shows extension contexts:
- **Background** - Service worker / background script
- **Content** - Content scripts
- **Popup** - Browser action popup
- **Options** - Options page
- **DevTools** - DevTools panel

With relationships showing message flows between them.

### 3. Component Diagrams

For selected contexts (default: background), shows:
- Message handlers
- UI components
- State management
- External integrations

### 4. Dynamic Diagrams

Shows message flow sequences:
- User action triggers
- Message propagation
- Handler execution
- API calls

## Features

✅ **Zero Configuration** - Works out of the box with manifest.json
✅ **TypeScript Native** - Analyzes your actual code, not annotations
✅ **Message Flow Tracing** - Tracks messages across context boundaries
✅ **API Detection** - Finds all external integrations automatically
✅ **Component Discovery** - Detects React/Preact components
✅ **Chrome API Usage** - Shows which Chrome APIs each context uses
✅ **JSDoc Support** - Respects `@description`, `@flow`, `@trigger` annotations

## CLI Usage

```bash
# Generate documentation
bunx web-ext-visualize

# Show help
bunx web-ext-visualize --help
```

## Programmatic Usage

```typescript
import { analyzeArchitecture, generateStructurizrDSL } from '@fairfox/web-ext-visualize'

// Analyze architecture
const analysis = await analyzeArchitecture({
  tsConfigPath: "./tsconfig.json",
  projectRoot: "."
})

// Generate Structurizr DSL
const dsl = generateStructurizrDSL(analysis, {
  includeDynamicDiagrams: true,
  includeComponentDiagrams: true,
  componentDiagramContexts: ["background"],
  styles: {
    background: "#2E7D32",
    popup: "#1976D2"
  }
})

console.log(dsl)
```

## Annotations

Enhance generated documentation with JSDoc comments:

```typescript
/**
 * @description Handles user authentication flow
 * @flow login-sequence
 * @trigger User clicks login button
 */
bus.on("USER_LOGIN", async (payload) => {
  // Handler implementation
})
```

Supported annotations:
- `@description` - Component/handler description
- `@flow` - Group related message handlers into named flows
- `@trigger` - What triggers this flow (user action, event, etc.)

## Output

Generated files in `docs/`:
- `architecture.dsl` - Structurizr DSL file

## Viewing Diagrams

### Option 1: Structurizr Lite (Docker)

```bash
cd docs
docker run -it --rm -p 8080:8080 \
  -v $(pwd):/usr/local/structurizr \
  structurizr/lite
```

Open http://localhost:8080

### Option 2: Structurizr Cloud

1. Go to https://structurizr.com
2. Create a workspace
3. Upload `docs/architecture.dsl`

### Option 3: VS Code Extension

Install "Structurizr" extension and open `architecture.dsl`

## Example Output

For a typical extension, generates:

```
workspace "My Extension" {
  model {
    user = person "User"

    authAPI = softwareSystem "Auth API"

    extension = softwareSystem "My Extension" {
      background = container "Background" {
        loginHandler = component "Login Handler"
        stateManager = component "State Manager"
      }

      popup = container "Popup" {
        loginForm = component "Login Form"
        todoList = component "Todo List"
      }

      user -> popup "Uses"
      popup -> background "Sends USER_LOGIN"
      background -> authAPI "POST /auth/login"
    }
  }

  views {
    systemContext extension { ... }
    container extension { ... }
    component background { ... }
    dynamic extension "Login Flow" { ... }
  }
}
```

## Requirements

- TypeScript project with `tsconfig.json`
- Chrome extension with `manifest.json`
- Built with `@fairfox/web-ext` (or compatible message-passing patterns)

## Architecture

Uses `@fairfox/web-ext-analysis` to:
1. Parse `manifest.json`
2. Extract TypeScript types
3. Trace message handlers
4. Detect external integrations
5. Build complete architecture model

Then generates Structurizr DSL following C4 model conventions.

## License

MIT
