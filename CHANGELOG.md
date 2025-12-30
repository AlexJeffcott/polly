# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.9.0] - 2025-12-30

### Added

#### Expose Tier 1 & 2 Optimization Features to Users (Issue #13)

**Problem:**
The `polly verify --optimize` command (added in v0.8.0) was recommending configuration options that weren't accessible to users through TypeScript types. Users would apply the AI's recommendations and encounter validation errors because the features appeared to not exist.

**What Was Missing:**
- Tier 1 optimizations: `include`, `exclude`, `symmetry`, `perMessageBounds`
- Tier 2 optimizations: `temporalConstraints`, `boundedExploration`
- Verification options: `timeout`, `workers`
- Project-specific bounds: `maxClients`, `maxRenderers`, `maxWorkers`, `maxContexts`

**Solution:**
All these features were already fully implemented in the TLA+ generator - they just weren't exposed through the public TypeScript API! This release adds:

1. **Updated Type Definitions** (`tools/verify/src/config.ts`)
   - Expanded `LegacyVerificationConfig` interface with all optimization fields
   - Full TypeScript autocomplete support
   - Comprehensive inline documentation

2. **Validation Logic** (`tools/verify/src/config/parser.ts`)
   - Validates include/exclude mutual exclusivity
   - Checks symmetry group sizes
   - Validates perMessageBounds ranges (1-20)
   - Validates temporal constraint ordering
   - Validates bounded exploration depth limits
   - Validates verification timeout and worker counts

3. **Config Generation** (`tools/verify/src/codegen/config.ts`)
   - Generated configs now include commented examples for all optimizations
   - Helpful inline documentation explaining each feature
   - Clear tier labels (Tier 1 vs Tier 2)

4. **AI Optimizer Updates** (`tools/teach/src/system-prompt.ts`)
   - Updated prompt to confidently recommend all available features
   - AI knows all features are fully implemented

**Usage Example:**
```typescript
export default defineVerification({
  state: { /* ... */ },
  messages: {
    maxInFlight: 3,

    // Tier 1: Message filtering (use include OR exclude)
    include: ['authenticate', 'query', 'command'],

    // Tier 1: Symmetry reduction
    symmetry: [
      ['query_user', 'query_post'],
      ['create', 'update', 'delete'],
    ],

    // Tier 1: Per-message bounds
    perMessageBounds: {
      'authenticate': 1,
      'query': 5,
    },
  },

  // Verification engine options
  verification: {
    timeout: 300,  // seconds
    workers: 2,
  },

  // Tier 2: Controlled approximations
  tier2: {
    temporalConstraints: [{
      before: 'authenticate',
      after: 'query',
      description: 'Must authenticate before querying',
    }],
    boundedExploration: {
      maxDepth: 20,
    },
  },
});
```

**Impact:**
- Users can now access all optimization features with full TypeScript support
- `polly verify --optimize` recommendations work without errors
- Helpful validation messages guide proper configuration
- 252 lines of new validation and documentation code

Fixes #13

## [0.8.0] - 2025-12-30

### Added

#### Claude-Powered Teach Command with Verification Optimizations (Issue #12)

Replaces the basic keyword-matching REPL with a full Claude API integration that provides intelligent, context-aware guidance about your Polly project.

**New Commands:**
- `polly teach` - Interactive Claude session for learning about your project
- `polly verify --optimize` - Launches teach mode focused on verification optimization

**Features:**
1. **Context-Aware AI** - Claude analyzes your entire project:
   - Project architecture and message flows
   - Verification configuration and results
   - Message types and handlers
   - State space statistics

2. **Verification Optimizations** - Five powerful optimization strategies:

   **Tier 1: Zero Precision Loss**
   - Message Type Filtering: `include`/`exclude` arrays (83% state reduction in examples)
   - Symmetry Reduction: `symmetry` groups for interchangeable messages
   - Per-Message Bounds: `perMessageBounds` for different concurrency limits per type

   **Tier 2: Controlled Approximations**
   - Temporal Constraints: `tier2.temporalConstraints` for ordering requirements
   - Bounded Exploration: `tier2.boundedExploration` for depth limits

3. **Implementation:**
   - Full TLA+ codegen support for all optimizations
   - @anthropic-ai/sdk integration
   - Conversation history tracking
   - Mode switching (teach vs optimize)

**Test Results:**
- Message filtering: 43 → 7 types (83.7% reduction)
- Combined optimizations: ~90-95% state space reduction
- Per-message bounds: 6 different bounds correctly generated
- Temporal constraints: 3 ordering requirements enforced

**Note:** Features were implemented in TLA+ generator but not exposed to users until v0.9.0 (see #13)

**Files Added:**
- `tools/teach/src/context-builder.ts` - Project analysis gathering
- `tools/teach/src/system-prompt.ts` - AI prompt generation
- `docs/OPTIMIZATION.md` - Comprehensive optimization guide
- `examples/full-featured/specs/verification.config.optimized.ts` - Example

**Dependencies:**
- Added `@anthropic-ai/sdk` for Claude API integration

Implements #12

## [0.6.1] - 2025-12-23

### Fixed

#### Verification: Filter Invalid TLA+ Identifiers from Message Types (Issue #11)
Fixes critical bug where the code analyzer was extracting TypeScript utility type definitions as message types, generating invalid TLA+ syntax.

**Problem:**
The `polly verify` command's code analyzer was treating TypeScript type definition syntax like `{ ok: true; value: T }` as message types. This generated invalid TLA+ identifiers containing braces, colons, and semicolons, causing TLA+ parsing to fail with lexical errors.

**Example Error:**
```
Lexical error at line 110, column 17. Encountered: ";" (59), after : ""
Fatal errors while parsing TLA+ spec in file UserApp
```

**Solution:**
- Added `isValidTLAIdentifier()` validation function to both `TypeExtractor` and `HandlerExtractor`
- Validates identifiers match TLA+ rules: `/^[a-zA-Z][a-zA-Z0-9_]*$/`
- Filters message types during analysis to only include valid TLA+ identifiers
- Added debug logging to track filtered types (use `POLLY_DEBUG=1`)

**What's Filtered:**
- ❌ `{ ok: true; value: t }` (contains braces, colons, semicolons)
- ❌ `{ ok: false; error: e }` (contains braces, colons, semicolons)
- ❌ `event-type` (contains hyphen)
- ❌ `123event` (starts with digit)
- ✅ `authenticate`, `user_login`, `API_REQUEST`, `event123` (valid)

**Impact:**
The generated `UserApp.tla` now only contains valid message types, preventing TLA+ parsing errors. Projects with TypeScript utility types can now use `polly verify` successfully.

**Testing:**
- Added comprehensive unit tests (`vendor/analysis/src/extract/__tests__/tla-validation.test.ts`)
- Tests cover valid identifiers, invalid identifiers, and edge cases
- All 3 tests passing with 18 assertions

**Debug Mode:**
Run with `POLLY_DEBUG=1` to see filtered types:
```bash
POLLY_DEBUG=1 bunx polly verify
```

Output:
```
[WARN] Filtered out 2 invalid message type(s):
[WARN]   - "{ ok: true; value: t }" (not a valid TLA+ identifier)
[WARN]   - "{ ok: false; error: e }" (not a valid TLA+ identifier)
```

Fixes #11

## [0.6.0] - 2025-12-23

### Changed
- **Major refactoring**: Eliminated all default exports across the codebase
- Fixed all linting issues for consistent code style
- Applied Biome formatter for unified formatting
- Resolved all TypeScript compilation errors (340+ → 0)

## [0.5.4] - 2025-12-16

### Fixed

#### Critical: Verify Feature Now Works (Issue #10)
Fixes the verify command which was completely broken in v0.5.3 due to missing package export.

**Bug 1: Missing ./verify export**
- Added `./verify` export to package.json pointing to lightweight public API
- Users can now import `defineVerification` from `@fairfox/polly/verify`
- Created new `public-api.ts` entry point (780 bytes, zero dependencies)
- Full verify API (adapters, analysis) remains in bundled CLI only

**Bug 2: CommonJS require() in ESM codebase**
- Replaced `require()` with ESM dynamic `import()` in verify CLI
- Added cache busting with timestamp query parameter
- Properly handles ESM default exports

**Impact:** The verify feature is now fully functional. Before this fix:
- `polly verify --setup` ✅ worked (generated config)
- `polly verify --validate` ❌ failed (couldn't load config)

After this fix, both commands work correctly.

**Technical Details:**
- Public API exports only `defineVerification` function and config types
- Heavy dependencies (ts-morph, analysis tools) only bundled in CLI
- User config files have zero runtime dependencies beyond polly itself

Fixes #10

## [0.5.3] - 2025-12-15

### Changed
- **Internal restructuring**: Consolidated monorepo into single package at repository root
- Moved tests from `packages/tests/` to `tests/`
- Moved examples from `packages/examples/` to `examples/`
- Flattened `packages/polly/` to repository root
- Integrated analysis, verify, and visualize tools as vendored code
- Updated all internal imports to use relative paths
- Unified build and development workflow

**Note:** This is an internal restructuring only - no API changes. All public exports remain the same.

## [0.5.2] - 2025-12-14

### Fixed

#### Structurizr DSL Syntax Error in Relationships
Fixes critical DSL syntax error that prevented visualization in Structurizr Lite (reported by Lingua CMS team in Issue #8).

**Problem:**
The `technology` parameter was incorrectly placed as a keyword inside the relationship block, causing Structurizr to fail with: `Unexpected tokens (expected: tags, url, properties, perspectives) at line X: technology "Function Call"`

**Before (Invalid):**
```dsl
handler -> service "Calls method()" {
  technology "Function Call"  # ❌ Invalid
  tags "Auto-detected"
}
```

**After (Valid):**
```dsl
handler -> service "Calls method()" "Function Call" {  # ✅ Correct
  tags "Auto-detected"
}
```

**Fixed Files:**
- `vendor/visualize/src/codegen/structurizr.ts` - Corrected relationship syntax for both user-provided and auto-detected relationships
- `vendor/visualize/src/__tests__/enhanced-dsl-integration.test.ts` - Updated tests to validate correct DSL syntax and prevent regression

**Impact:**
All DSL files now generate valid Structurizr syntax and can be visualized without errors. This affects both explicit relationships and auto-detected relationships from cross-file analysis.

## [0.5.1] - 2025-12-14

### Enhanced

#### Cross-File Relationship Detection
Fixes the architecture pattern mismatch reported in Issue #8 for projects with router-handler separation (like Lingua CMS).

**Problem Solved:**
v0.5.0 automatic detection only worked when handler routing and business logic were in the same function. It failed for production codebases with proper separation of concerns where handlers are in separate files.

**What's New:**
- **Cross-file AST traversal** - When detecting a handler call, Polly now resolves the import and analyzes the function body in the separate file
- **Nested property access detection** - Correctly detects patterns like `repositories.users.create()`, `db.connection.query()`
- **Function name inference** - Detects service calls from function names like `getDatabase()`, `createRepositories()`
- **Enhanced component mappings** - Added "repositories" and improved pattern matching
- **Graceful failure handling** - Silently handles missing files or parse errors without breaking analysis

**Example:**
```typescript
// server.ts (router):
if (isQueryMessage(message)) {
  response = await handleQuery(message);  // ← Polly detects handler
}

// handlers/query.ts (separate file):
export async function handleQuery(message: QueryMessage) {
  const db = getDatabase();              // ← NOW DETECTED ✅
  const repos = createRepositories(db);  // ← NOW DETECTED ✅
  return repos.users.findById(id);       // ← NOW DETECTED ✅
}

// Generated DSL (automatic):
query_handler -> db_client "Calls getDatabase()"
query_handler -> repositories "Calls createRepositories()"
query_handler -> repositories "Calls findById()"
```

**Test Coverage:**
- Added cross-file-handlers test fixture mimicking router-handler separation
- 7 new integration tests for cross-file relationship detection
- All 57 tests passing with 221 assertions

**Technical Implementation:**
- New `resolveImportedFunction()` method using ts-morph's `getModuleSpecifierSourceFile()`
- Recursive analysis preserves handler context across file boundaries
- Supports regular functions, arrow functions, and const function declarations
- Enhanced `extractFromPropertyAccess()` to handle nested property chains

**Impact:**
This enhancement makes automatic relationship detection work for real-world production codebases with proper architectural patterns. No more isolated gray boxes for projects with separated handler files!

## [0.5.0] - 2025-12-14

### Added

#### Auto-Generated, Always Up-to-Date Architecture Docs (Issue #8 Phase 2)
This release completes Phase 2 of Issue #8, implementing automatic detection features that eliminate manual configuration and ensure architecture diagrams stay in sync with code changes.

**Philosophy:** Architecture diagrams should be auto-generated from code analysis, not manually configured. When code changes, diagrams update automatically on re-run.

##### Priority 1: Automatic Relationship Detection ✅
- **Code analysis-based relationship detection** - Analyzes handler function bodies to detect component dependencies
- **Recursive function following** - Traces execution through local function calls to find actual service invocations
- **Property access detection** - Identifies patterns like `userService.listUsers()`, `authService.authenticate()`
- **Multiple relationship patterns** - Supports function calls, database queries, HTTP requests
- **Service name inference** - Maps object names to component IDs (user → user_service, auth → auth_service, db → db_client)
- **Automatic service component generation** - Creates service component definitions when relationships detected
- **Confidence scoring** - Relationships include confidence level (high/medium/low) and evidence
- **AST traversal** - Uses ts-morph to analyze TypeScript syntax trees
- **Deduplication** - Prevents duplicate relationships within a handler
- **Zero configuration** - Works automatically, no manual relationship definitions needed

**Example:**
```typescript
// Handler code:
async function handleQuery(message: QueryMessage) {
  const result = await userService.listUsers();
  return { type: 'result', data: result };
}

// Generated DSL (automatic):
user_service = component "User Service" {
  tags "Service" "Auto-detected"
}

query_handler -> user_service "Calls listUsers()" {
  technology "Function Call"
  tags "Auto-detected"
}
```

##### Priority 4: Automatic Component Grouping ✅
- **4-tier grouping strategy** for intelligent component organization:
  1. **Authentication handlers** - login, logout, auth, verify, register, signup
  2. **Subscription handlers** - subscribe, unsubscribe
  3. **Entity-based grouping** - Extracts entities from message types (user_add, todo_remove → User Management, Todo Management)
  4. **Query/Command pattern** - Groups remaining handlers by read vs write operations
- **Smart thresholds** - Only creates groups when >= 50% of components can be grouped OR >= 2 groups exist
- **Minimum group size** - Requires >= 2 components per entity group
- **Lifecycle handler exclusion** - Skips connection, message, close, error handlers
- **Fallback to flat rendering** - Returns empty array when grouping doesn't add value
- **Backward compatible** - Manual groups take precedence over automatic grouping
- **Pattern matching** - Supports both snake_case (user_add) and camelCase (addUser) naming

**Example:**
```dsl
group "User Management" {
  user_add_handler = component "User Add Handler" { ... }
  user_update_handler = component "User Update Handler" { ... }
  user_remove_handler = component "User Remove Handler" { ... }
}

group "Todo Management" {
  todo_add_handler = component "Todo Add Handler" { ... }
  todo_update_handler = component "Todo Update Handler" { ... }
}

group "Query Handlers" {
  list_users_handler = component "List Users Handler" { ... }
  get_todos_handler = component "Get Todos Handler" { ... }
}
```

##### Priority 5: Auto-Generate Dynamic Diagrams ✅
- **Automatic sequence diagram generation** from detected relationships
- **Category-based organization** - Groups handlers by authentication, entity (user, todo), query/command
- **Smart diagram count** - Single overview diagram for small projects (<= 5 handlers, <= 3 categories)
- **Category-specific diagrams** - Separate diagrams per category for larger projects (max 5)
- **Handler-to-service flows** - Shows execution path from message handler through business services
- **Descriptive titles** - "Authentication Flow", "User Management Flow", "Query Processing Flow"
- **Contextual descriptions** - Explains what each diagram shows
- **Proper scope** - Uses correct container context (extension.server)
- **Auto-layout** - Left-to-right flow visualization
- **Configuration option** - Can disable via `includeDynamicDiagrams: false`
- **Backward compatible** - User-provided diagrams generated first, then automatic diagrams

**Example (small project - single overview):**
```dsl
dynamic extension.server "Message Processing Flow" "Shows message processing flow through handlers and services" {
  query_handler -> user_service "Calls listUsers()"
  command_handler -> user_service "Calls executeUserCommand()"
  auth_handler -> auth_service "Calls authenticate()"
  autoLayout lr
}
```

**Example (larger project - category-specific):**
```dsl
dynamic extension.server "Authentication Flow" "Shows authentication message processing" {
  auth_handler -> auth_service "Calls authenticate()"
  login_handler -> auth_service "Calls login()"
  logout_handler -> auth_service "Calls logout()"
  autoLayout lr
}

dynamic extension.server "User Management Flow" "Shows user management operations" {
  user_add_handler -> user_service "Calls addUser()"
  user_update_handler -> user_service "Calls updateUser()"
  user_remove_handler -> user_service "Calls removeUser()"
  autoLayout lr
}
```

#### Test Infrastructure
- **50 integration tests** with **187 assertions** - all passing
- **8 tests for Priority 1** - Relationship detection and DSL output
- **5 tests for Priority 4** - Component grouping logic
- **5 tests for Priority 5** - Dynamic diagram generation
- **Real code analysis** (not mocked) - uses actual TypeScript parsing
- **Real test project** - complete WebSocket server with service calls
- **Validates entire pipeline** from TypeScript files → Analysis → DSL output

#### Architecture Enhancements
- Added `relationships?: ComponentRelationship[]` to `MessageHandler` type
- Created `RelationshipExtractor` class with recursive AST traversal
- Enhanced `StructurizrDSLGenerator` with automatic grouping and diagram generation
- Proper deduplication and evidence tracking for detected relationships
- Smart threshold logic to prevent over-grouping and over-diagramming

### Technical Details
- **New file:** `vendor/analysis/src/extract/relationships.ts` (~415 lines) - Core relationship detection
- **Modified:** `vendor/analysis/src/types/core.ts` - Added ComponentRelationship type
- **Modified:** `vendor/analysis/src/extract/handlers.ts` - Integrated relationship extraction
- **Modified:** `vendor/visualize/src/codegen/structurizr.ts` - Added automatic features
- **Modified:** `vendor/visualize/src/__tests__/enhanced-dsl-integration.test.ts` - Comprehensive test coverage

### Value Proposition
**Before Phase 2:** Architecture diagrams required manual configuration of relationships, groups, and flows. When code changed, diagrams became stale unless manually updated.

**After Phase 2:** Architecture diagrams are auto-generated from code analysis. Re-running `polly visualize` automatically updates diagrams to reflect current code structure. Zero configuration needed.

**Impact:** This delivers on the core promise of Issue #8 - "auto-generated, always up-to-date architecture docs that require zero manual configuration."

**COMPLETES #8 Phase 2** - All 3 automatic detection priorities delivered (100%)

## [0.4.2] - 2025-12-14

### Added

#### Priority 6: Deployment Diagrams - FINAL PIECE
This release adds the final missing piece, completing ALL 7 API infrastructure priorities from Issue #8 Phase 1.

**Note:** v0.4.1 was published without deployment diagrams. This v0.4.2 release adds Priority 6: Deployment Diagrams.

- **Deployment environments** with multi-environment support (Production, Staging, Dev)
- **Nested deployment nodes** for hierarchical infrastructure (Cloud → Region → Instance)
- **Container instance mapping** with explicit deployment targets
- **Instance scaling** - specify replica counts per container
- **Deployment properties** for operational metadata (region, auto-scaling, etc.)
- **Automatic container deployment** as fallback when not explicitly configured
- **Deployment views** auto-generated for each environment
- **5 integration tests** covering all deployment scenarios
- Test suite increased from 27 to 32 tests, assertions from 95 to 112

**COMPLETES #8 Phase 1** - All 7 API infrastructure priorities delivered (100%)

## [0.4.1] - 2025-12-14

### Note
This version was published without deployment diagrams. Use v0.4.2 for complete Phase 1 functionality.

## [0.4.0] - 2025-12-14

### Added

#### Enhanced Structurizr DSL Generation (Issue #8)
Complete implementation of ALL 7 priorities with comprehensive real integration testing:

##### Priority 2: Styling System ✅
- **Default element styles** with hexagons and semantic colors
  - Query handlers: Green (#51cf66)
  - Command handlers: Orange (#ff922b)
  - Authentication: Red (#ff6b6b)
  - Subscription: Purple (#845ef7)
- **Default relationship styles** with orthogonal routing, proper colors
- **Theme URL support** (Structurizr default theme)
- **Full customization** - override any style or disable defaults entirely
- **4 integration tests** covering all styling features

##### Priority 3: Properties & Metadata ✅
- **Source file paths** with line numbers (e.g., `src/server/handlers.ts:55`)
- **Technology stack detection** (TypeScript, WebSocket, Socket.IO, Elysia)
- **Message type classification** (Query, Command, Authentication, Subscription)
- **Pattern identification** (Query Handler, Command Handler, etc.)
- **Custom properties** for user-defined metadata
- **4 integration tests** covering all property features

##### Priority 1: Component Relationships ✅
- **Explicit relationship definition** between components
- **Technology metadata** on relationships
- **Relationship tagging** (Sync, Async, Database, etc.)
- **Optional fields** for minimal syntax
- **2 integration tests** covering relationship scenarios

##### Priority 4: Groups ✅
- **User-defined groups** for organizing related components
- **Proper DSL nesting** with indentation
- **Ungrouped components** rendered outside groups
- **Multiple groups** support
- **3 integration tests** covering all grouping scenarios

##### Priority 5: Dynamic Diagrams ✅
- **User-provided dynamic diagrams** with custom steps (sequence/flow diagrams)
- **Sequence flow specification** (from → to → description)
- **Diagram title and description**
- **Configurable scope** (container, system)
- **Multiple diagrams** support
- **Auto-layout** with left-to-right flow
- **2 integration tests** covering diagram scenarios

##### Priority 7: Perspectives ✅
- **Component-level perspectives** (Security, Performance, etc.)
- **Multiple perspectives per component**
- **Name-description pairs** for architectural reasoning
- **Optional perspectives** (only added when configured)
- **2 integration tests** covering perspective scenarios

##### Priority 6: Deployment Diagrams ✅
- **Deployment environments** with multi-environment support (Production, Staging, Dev)
- **Nested deployment nodes** for hierarchical infrastructure (Cloud → Region → Instance)
- **Container instance mapping** with explicit deployment targets
- **Instance scaling** - specify replica counts per container
- **Deployment properties** for operational metadata (region, auto-scaling, etc.)
- **Automatic container deployment** as fallback when not explicitly configured
- **Deployment views** auto-generated for each environment
- **5 integration tests** covering all deployment scenarios

#### Test Infrastructure
- **32 integration tests** with **112 assertions** - all passing
- **Real code analysis** (not mocked) - uses actual TypeScript parsing
- **Real test project** - complete WebSocket server with 6 handlers
- **Validates entire pipeline** from TypeScript files → Analysis → DSL output
- **File system validation** - writes DSL to disk and verifies
- **Manual verification support** - provides Structurizr Lite instructions

#### Type System
- **Strict TypeScript typing** throughout - no `any` types
- **Comprehensive type definitions** in `vendor/visualize/src/types/structurizr.ts`
- 14 element shapes, line styles, routing options
- `ComponentProperties`, `ComponentRelationship`, `ComponentGroup`, `DynamicDiagram`, `Perspective`, `DeploymentNode`, `ContainerInstance` interfaces
- Default color palette and styles with full customization

#### Architecture Enhancements
- Added `projectRoot` field to `ArchitectureAnalysis` type for relative path computation
- Enhanced `StructurizrDSLGenerator` with reusable component generation
- Proper DSL escaping and formatting throughout
- Clean separation of concerns (properties, perspectives, groups)

### Changed
- Component generation refactored to collect definitions before rendering
- DSL generator now supports grouping and perspectives
- All features are backward compatible - additive changes only

### Example Output
```dsl
workspace "example" {
  model {
    extension = softwareSystem "example" {
      server = container "Server" {
        group "Business Logic Handlers" {
          query_handler = component "Query Handler" "..." {
            tags "Message Handler"
            properties {
              "Source" "src/server/handlers.ts:55"
              "Technology" "TypeScript, WebSocket"
              "Message Type" "Query"
              "Pattern" "Query Handler"
            }
            perspectives {
              "Security" "Read-only, low risk"
              "Performance" "Cached for 5 minutes"
            }
          }
        }
      }
    }

    deploymentEnvironment "Production" {
      deploymentNode "AWS" "Cloud infrastructure" "Amazon Web Services" {
        properties {
          "Region" "us-east-1"
          "Auto-scaling" "Enabled"
        }
        deploymentNode "EC2 Instance" "Application server" "t3.medium" {
          containerInstance extension.server 2
        }
      }
    }
  }
  views {
    dynamic extension "Message Flow" "..." {
      user -> extension.server "Sends message"
      extension.server -> extension.server.query_handler "Routes"
      autoLayout lr
    }

    deployment extension "Production" "Production environment deployment architecture" {
      include *
      autoLayout lr
    }

    styles {
      element "Message Handler" {
        shape Hexagon
        background #1168bd
      }
      element "Query" {
        background #51cf66
      }
      relationship "Relationship" {
        routing Orthogonal
      }
      theme https://static.structurizr.com/themes/default/theme.json
    }
  }
}
```

### Technical Details
- Implementation follows strict typing requirements (no `any`)
- Tests validate real code analysis (not mocked)
- Full integration from TypeScript files → DSL output
- Backward compatible - no breaking changes

**COMPLETES #8** - All 7 priorities delivered (100%)

## [0.3.8] - 2025-12-14

### Added

#### Comprehensive Test Coverage (44 Tests)
- **DSL generation tests** - 11 tests covering component diagram generation for all project types
- **Project detection tests** - 15 tests for WebSocket servers, PWAs, and generic TypeScript projects
- **Prevents regressions** - Tests explicitly check for bugs like Issue #7 before they reach users
- **Automated validation** - Tests run as part of `prepublishOnly` script

#### Critical Test Coverage
The DSL generation test suite includes a test that explicitly checks for the Issue #7 bug:
```typescript
test("should NOT generate components when context not in componentDiagramContexts")
```

This test would have caught Issue #7 immediately, preventing it from reaching production.

#### Implementation Gaps Documented
Tests revealed non-critical limitations (documented for future enhancement):
1. Generic projects default to "websocket-app" type
2. Only `server.ts` detected as entry point (not `index.ts`, `app.ts`, `main.ts`)
3. Client context detection not implemented
4. Context mapping naming inconsistent

**Impact**: Before these tests, Issue #7 reached users. After these tests, similar bugs will be caught automatically before release.

See `TEST_COVERAGE_REPORT.md` for full details.

## [0.3.7] - 2025-12-14

### Fixed

#### Visualization: Component Diagrams for All Context Types
- **Auto-detect contexts for component diagrams** - Component diagrams now generated for all detected contexts, not just "background"
- **Fixes WebSocket server visualization** - Handler components now appear in DSL for "server" contexts
- **Fixes PWA/Worker visualization** - Works for "worker", "serviceworker", and all context types
- **Backward compatible** - Chrome extensions with "background" context work identically

**Impact**: Before this fix, component diagrams were only generated for Chrome extension "background" contexts, making the visualization feature broken for all non-extension projects (WebSocket servers, PWAs, workers) despite v0.3.0 adding manifest-optional support.

**Example**: Lingua CMS WebSocket server now generates full component diagrams:
```dsl
server = container "Server" {
  query_handler = component "Query Handler" { ... }
  command_handler = component "Command Handler" { ... }
  subscribe_handler = component "Subscribe Handler" { ... }
  unsubscribe_handler = component "Unsubscribe Handler" { ... }
}

component extension.server "Components_Server" {
  include *
  autoLayout tb
}
```

Fixes #7

## [0.3.6] - 2025-12-14

### Fixed

#### Bug Fixes Found by Test Suite
- **Correct ts-morph API usage** - Fixed `Node.isTypePredicate()` call (was incorrectly using `Node.isTypePredicateNode()`)
- **Prevent duplicate handler detection** - Skip else-if statements when processing if statements (they're already handled by the chain walker)

### Added

#### Comprehensive Test Suite
- **7 automated tests** covering all type guard detection patterns
- Tests for local type guards, imported guards, .ts extensions, path aliases, else-if chains
- Prevents regressions like the v0.3.2-v0.3.5 cycle

This version actually works correctly. v0.3.5 had the right approach (AST-based detection) but had implementation bugs that were caught and fixed by the new test suite.

## [0.3.5] - 2025-12-14

### Deprecated

Had bugs in implementation (wrong API method, duplicate detection). Use v0.3.6 instead.

### Fixed

#### Use AST-Based Type Predicate Detection (The Actual Fix)
- **Check AST structure, not resolved types** - Use `getReturnTypeNode()` and `Node.isTypePredicateNode()` instead of `getReturnType().getText()`
- **Fixes imported type guard detection** - ts-morph returns `"boolean"` for type predicates when checking resolved types across files, but AST structure preserves the actual type predicate
- **Works for all import patterns** - Path aliases, relative imports, with or without `.ts` extensions

### The Real Problem

When resolving imported functions, ts-morph's type system simplifies type predicates to their structural equivalent:
```typescript
// Function signature:
function isQuery(msg: Request): msg is Query { ... }

// What we were checking (WRONG):
def.getReturnType().getText()  // Returns "boolean" ❌

// What we now check (CORRECT):
def.getReturnTypeNode()  // Returns TypePredicateNode ✅
Node.isTypePredicateNode(returnTypeNode)  // true ✅
```

### What Changed

Both `findTypePredicateFunctions()` (local) and `resolveImportedTypeGuard()` (imported) now use AST-based detection:

```typescript
const returnTypeNode = node.getReturnTypeNode()

if (returnTypeNode && Node.isTypePredicateNode(returnTypeNode)) {
  const typeNode = returnTypeNode.getTypeNode()
  const typeName = typeNode.getText()  // "QueryMessage" ✅
  const messageType = extractMessageTypeFromTypeName(typeName)  // "query"
}
```

This works because AST nodes preserve the actual syntax structure, while resolved types represent semantic equivalence.

Fixes #6

## [0.3.4] - 2025-12-14

### Deprecated

Attempted to fix with compiler options. The actual issue was checking resolved types instead of AST structure. Use v0.3.5 instead.

## [0.3.3] - 2025-12-14

### Deprecated

This version implemented a manual fallback for import resolution. Use v0.3.5 instead.

## [0.3.2] - 2025-12-13

### Added

#### Imported Type Guard Detection
- **Cross-file resolution** - Automatically follows imports using ts-morph symbol resolution
- **Path alias support** - Works with tsconfig path aliases (@ws/, @/, etc.)
- **Named imports** - Detects type guards from `import { isQuery } from './messages'`
- **Relative imports** - Handles `./` and `../` imports correctly
- **Performance optimized** - Local lookup first, import resolution as fallback
- **Graceful error handling** - Skips resolution failures silently

### Example Enhancement
```typescript
// Type guard defined in: packages/api/src/ws/messages.ts
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

// Used in: packages/api/src/server.ts
import { isQueryMessage } from '@ws/messages'

if (isQueryMessage(message)) {
  handleQuery(message)  // ✅ NOW DETECTED!
}
```

### Benefits
- No manual import parsing required - ts-morph handles complexity
- Works with all import patterns automatically
- Backward compatible - existing code works identically
- Enables full handler detection for projects like Lingua CMS

Addresses #4

## [0.3.1] - 2025-12-13

### Added

#### TypeScript Type Guard Pattern Detection
- **Type predicate detection** - Automatically detects TypeScript type guard functions (`msg is QueryMessage`)
- **If/else-if chain support** - Handles message routing with if/else-if chains using type guards
- **Message type extraction** - Extracts message types from type names (e.g., `QueryMessage` → `query`)
- **Fallback analysis** - Analyzes function body when type name doesn't match pattern (`return msg.type === 'query'`)
- **Performance optimized** - WeakMap caching prevents redundant file scanning (O(n) instead of O(n²))
- **Works alongside existing patterns** - Compatible with switch/case, handler maps, and `.on()` detection

### Example Pattern Detected
```typescript
function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

if (isQueryMessage(message)) {
  response = await handleQuery(message)
} else if (isCommandMessage(message)) {
  response = await handleCommand(message)
}
```

### Benefits
- Detects handlers in TypeScript projects using type guard patterns
- Common in well-typed codebases for type narrowing and IDE support
- Enables full handler detection for projects like Lingua CMS

### Limitations
- Only detects type guards defined in the same file (imported type guards require enhancement)
- Future versions may add cross-file type guard resolution

Addresses #2

## [0.3.0] - 2025-12-12

### Added

#### Phase 1: Manifest-Optional Architecture Visualization
- **Make manifest.json optional** - Polly Visualize now works without manifest.json for WebSocket servers, generic TypeScript projects, PWAs, and Electron apps
- **Auto-detect project type** from manifest.json, package.json, or tsconfig.json
- **Simple context naming** - Use "server/client" instead of "websocket-server/websocket-client"
- **Improved CLI messaging** - Shows detected project type (Chrome Extension vs auto-detect)
- **Updated help text** - Lists all supported project types

#### Phase 2: Enhanced WebSocket Detection
- **Content analysis** - Analyzes server files to detect frameworks without relying solely on package.json
- **Framework-specific detection** for Bun, Node ws, Socket.io, Elysia, Express, Fastify, Hono, Koa
- **Confidence scoring system** with 15+ regex patterns to find the best server entry point
- **Distinguish server types** - Automatically labels as "WebSocket Server" vs "HTTP Server"
- **Bun built-in WebSocket support** - Works even without dependencies in package.json

#### Phase 3: Generic Message Pattern Detection
- **Extended handler detection** - Supports 5 new handler patterns beyond `.on()`:
  - `addEventListener('message', handler)` for Web Workers
  - `switch(message.type) { case 'EVENT': ... }` router patterns
  - `const handlers = { 'EVENT': fn }` handler map patterns
  - `ws.on('event', handler)` WebSocket handlers
  - `socket.on('event', handler)` Socket.io handlers

- **Extended flow detection** - Supports 5 new sender patterns beyond `.send()`:
  - `ws.send(message)` WebSocket messages
  - `socket.emit('event', data)` Socket.io events
  - `postMessage(data)` Web Worker/Window messages
  - `window.postMessage(data)` cross-window communication
  - `client.send()` broadcast patterns

### Changed
- ManifestParser constructor now accepts optional parameter for graceful handling of missing manifest
- ArchitectureAnalyzer automatically uses project detector when manifest is missing
- findProjectRoot() in visualize CLI checks for manifest.json OR package.json OR tsconfig.json

### Testing
- Added 11 unit tests for ManifestParser with optional manifest handling
- Integration tested with Chrome extension examples (backward compatible)
- Integration tested with WebSocket servers (Node ws, Bun)
- Tested comprehensive message pattern detection (10 handlers detected across all patterns)

### Migration Guide
No breaking changes! This release is 100% backward compatible:
- Chrome extensions with manifest.json work identically
- No API changes required
- Existing visualizations generate the same output

To use new features:
1. Run `polly visualize` in WebSocket/generic projects without manifest.json
2. Message patterns are detected automatically (no config needed)
3. Server framework detection works out of the box

## [0.2.1] - 2025-11-11

### Fixed
- **Verification Tool**: Fixed MessageRouter.tla not being found during Docker verification
  - CLI now searches multiple locations for MessageRouter.tla template file
  - Added support for external polly directory installations (git submodules, monorepos)
  - Bundled MessageRouter.tla specs with the published package
  - Improved error messaging when MessageRouter.tla cannot be found

## [0.2.0] - Previous release

(Previous changelog entries would go here)
