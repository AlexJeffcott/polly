# @fairfox/polly-visualize - Architecture

## System Overview

This package automatically generates architecture documentation (Structurizr DSL + C4 diagrams) by analyzing Chrome extension codebases.

## Package Structure

```
@fairfox/polly-visualize
├── src/
│   ├── codegen/
│   │   └── structurizr.ts      # DSL generator
│   ├── cli.ts                  # Command-line interface
│   └── index.ts                # Public API
├── package.json
└── README.md
```

## Dependencies

- **@fairfox/polly-analysis** - Provides all analysis capabilities
  - Type extraction
  - Manifest parsing
  - Context analysis
  - Flow tracing
  - Integration detection

## How It Works

### 1. Analysis Phase

Uses `@fairfox/polly-analysis` to extract:

```typescript
const analysis = await analyzeArchitecture({
  tsConfigPath: "./tsconfig.json",
  projectRoot: "."
})
```

Returns:
- **System info** - name, version, description
- **Manifest** - parsed manifest.json
- **Contexts** - background, content, popup, etc.
- **Message flows** - communication between contexts
- **Integrations** - external APIs, Chrome APIs, npm packages

### 2. Generation Phase

Transforms analysis into Structurizr DSL:

```typescript
const dsl = generateStructurizrDSL(analysis, {
  includeDynamicDiagrams: true,
  includeComponentDiagrams: true,
  componentDiagramContexts: ["background"]
})
```

### 3. Output Phase

Writes `docs/architecture.dsl` containing:
- System Context diagram
- Container diagram
- Component diagrams
- Dynamic diagrams (message flows)
- Custom styling

## Structurizr DSL Mapping

### Extension → System

```
Chrome Extension = softwareSystem
```

### Context → Container

```
background = container "Background"
popup = container "Popup"
content = container "Content"
```

### Handler → Component

```
loginHandler = component "Login Handler"
```

### Message Flow → Relationship

```
popup -> background "Sends USER_LOGIN"
```

### API Call → External System

```
authAPI = softwareSystem "Auth API"
background -> authAPI "POST /auth/login"
```

## Example Output

For a todo list extension:

```dsl
workspace "Todo List Example" {
  model {
    user = person "User"

    extension = softwareSystem "Todo List Example" {
      background = container "Background" {
        loginHandler = component "Login Handler"
        todoAddHandler = component "Todo Add Handler"
        todoToggleHandler = component "Todo Toggle Handler"
      }

      popup = container "Popup" {
        todoList = component "Todo List"
        loginForm = component "Login Form"
      }
    }

    user -> popup "Uses"
    popup -> background "Sends TODO_ADD"
    background -> authAPI "Calls"
  }

  views {
    systemContext extension { ... }
    container extension { ... }
    component background { ... }
  }
}
```

## CLI Usage

```bash
# From extension project root
bunx web-ext-visualize

# Outputs to:
# docs/architecture.dsl
```

## Programmatic Usage

```typescript
import {
  analyzeArchitecture,
  generateStructurizrDSL
} from '@fairfox/polly-visualize'

const analysis = await analyzeArchitecture({
  tsConfigPath: "./tsconfig.json",
  projectRoot: "."
})

const dsl = generateStructurizrDSL(analysis, {
  includeDynamicDiagrams: true,
  componentDiagramContexts: ["background", "content"]
})
```

## Extensibility

### Custom Styles

```typescript
const dsl = generateStructurizrDSL(analysis, {
  styles: {
    background: "#2E7D32",  // Green
    popup: "#1976D2",       // Blue
    content: "#F57C00"      // Orange
  }
})
```

### Custom Theme

```typescript
const dsl = generateStructurizrDSL(analysis, {
  theme: "https://example.com/my-theme.json"
})
```

## Tested With

✅ **Minimal Example** - Single background context, 1 handler
✅ **Todo List Example** - Background context, 8 handlers
✅ **Source file detection** - Handles manifest.json → TypeScript source mapping

## Future Enhancements

1. **Dynamic diagrams** - Show message flow sequences
2. **External API detection** - Detect fetch() calls
3. **UI components** - Extract React/Preact components
4. **Popup context** - Analyze popup HTML + scripts
5. **Content scripts** - Analyze content script injection
6. **ADR support** - Generate Architecture Decision Records
7. **Mermaid output** - Alternative diagram format
8. **Export** - PNG/SVG/PDF via Structurizr CLI

## Architecture Decisions

### Why Structurizr DSL?

- Industry standard (C4 model)
- Text-based (version control friendly)
- Multiple viewers available
- Supports multiple diagram types from single model
- Extensible with custom themes/styles

### Why Separate from Analysis?

- **Separation of concerns** - Analysis is domain-agnostic
- **Reusability** - Same analysis powers both verify and visualize
- **Testability** - Can test DSL generation independently
- **Performance** - Analysis runs once, multiple generators can use it

### Why C4 Model?

- Well-established notation
- Multiple levels of abstraction
- Supports both static and dynamic views
- Understood by architects and developers
- Tools ecosystem (Structurizr, PlantUML, etc.)

## Testing

Verified with real extension examples:

```bash
cd packages/examples/minimal
bun ../../visualize/src/cli.ts
# ✓ Generates valid DSL with 1 context, 1 handler

cd packages/examples/todo-list
bun ../../visualize/src/cli.ts
# ✓ Generates valid DSL with 1 context, 8 handlers
```

## Performance

- **Analysis:** ~1-2 seconds for small extension
- **Generation:** <100ms
- **Total:** ~2 seconds end-to-end

## Limitations

Current version:
- Only detects contexts with manifest entries
- Message flows detection is basic (finds .send() calls)
- No cross-file flow tracing yet
- No external API detection yet (planned)
- No popup component extraction yet (planned)

## License

MIT
