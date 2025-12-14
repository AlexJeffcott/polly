# Enhanced Structurizr DSL Implementation Plan

## Overview
Implementing Issue #8 - Rich Structurizr DSL generation with relationships, styling, properties, groups, and dynamic diagrams.

## Implementation Order

### Phase 1: Foundation & Styling (Quick Win) ✅
**Goal**: Professional-looking diagrams immediately

1. **Create strict types** ✅ DONE
   - `vendor/visualize/src/types/structurizr.ts`
   - All style, relationship, property types defined
   - Default colors and styles defined

2. **Implement enhanced styling system**
   - Update `StructurizrDSLOptions` to use new types
   - Rewrite `generateStyles()` method
   - Apply default styles based on tags
   - Support custom style overrides
   - Add theme support

3. **Real integration tests**
   - Create test project with handlers
   - Generate actual DSL
   - Verify styles are applied correctly
   - Test with Structurizr Lite

### Phase 2: Properties & Metadata
**Goal**: Traceability and context

1. **Extract component properties**
   - Source file path and line numbers (already available from handlers)
   - Technology (TypeScript)
   - Pattern (type-guard, switch-case, etc.)
   - Message type

2. **Generate properties in DSL**
   - Add properties block to components
   - Format correctly for Structurizr

3. **Real integration tests**
   - Verify properties are extracted
   - Verify DSL format is correct

### Phase 3: Component Relationships (Most Complex)
**Goal**: Show how components interact

1. **Create RelationshipAnalyzer class**
   - Extend existing import resolution (from type guard detection)
   - Detect function calls between components
   - Detect import usage
   - Detect database access patterns
   - Conservative detection (avoid false positives)

2. **Relationship types to detect**
   - Function calls: `someFunction()`
   - Method calls: `service.method()`
   - Import usage: `import { db } from './database'`
   - Property access: `this.repository.find()`

3. **Generate relationships in DSL**
   - Add relationship statements
   - Include technology tags
   - Add descriptions

4. **Real integration tests**
   - Create test project with clear relationships
   - Verify relationships detected correctly
   - Test performance with large codebase (Lingua CMS)
   - No false positives

### Phase 4: Groups
**Goal**: Organize components

1. **Auto-group detection**
   - By handler type (Query, Command, Auth)
   - By message type patterns
   - By file location

2. **Generate groups in DSL**

3. **Real integration tests**

### Phase 5: Dynamic Diagrams
**Goal**: Show message flows

1. **Generate dynamic diagrams from message flows**
   - One diagram per message type
   - Show sequence from handler → services → database → response
   - Requires relationships from Phase 3

2. **Real integration tests**
   - Verify sequences are correct
   - Test with Structurizr Lite

### Phase 6: Deployment Diagrams (Optional)
**Goal**: Show runtime context

1. **Detect deployment environment**
   - Bun/Node detection
   - Docker detection
   - Container orchestration

2. **Generate deployment diagrams**

### Phase 7: Perspectives (Optional)
**Goal**: Add architectural reasoning

1. **Add configurable perspectives**
   - Security, Performance, Reliability
   - User-provided via config

## Testing Strategy

### Unit Tests (Some, but minimal)
- Type validation
- DSL format verification
- Helper functions

### Integration Tests (PRIMARY FOCUS)
**Real projects, real analysis, real DSL generation**

1. **Test Project 1: Simple WebSocket Server**
   - server.ts with 2-3 handlers
   - database.ts with simple functions
   - services.ts with business logic
   - **Test**: Handlers detected, relationships found, DSL generated correctly

2. **Test Project 2: Multi-Context Application**
   - Multiple contexts (background, worker, server)
   - Cross-context message flows
   - **Test**: All contexts styled correctly, groups work

3. **Test Project 3: Complex Relationships**
   - Handlers calling services
   - Services calling repositories
   - Repositories calling database
   - **Test**: Full relationship chain detected

4. **Test Project 4: Lingua CMS (Real World)**
   - Large, real codebase
   - Performance test
   - **Test**: Analysis completes in reasonable time (<10s), accurate results

### Visual Verification Tests
For each test project:
1. Generate DSL
2. Load in Structurizr Lite
3. Screenshot and verify visually
4. Check for rendering errors

## Performance Requirements

- Analysis of medium codebase (~50 files): <5 seconds
- Analysis of large codebase (Lingua CMS): <10 seconds
- Memory usage: <500MB for large codebase
- No infinite loops or stack overflows

## Code Quality Requirements

1. **Strict typing throughout**
   - No `any` types
   - All functions have explicit return types
   - All parameters have explicit types

2. **Error handling**
   - Graceful degradation on analysis errors
   - Clear error messages
   - Never crash, always produce valid DSL

3. **Documentation**
   - JSDoc on all public methods
   - Inline comments for complex logic
   - Examples in type definitions

4. **Testing**
   - Real integration tests (not mocked)
   - Test actual DSL output
   - Verify with Structurizr Lite
   - Performance tests with real codebases

## Success Criteria

- [ ] All 7 priorities implemented
- [ ] Strict typing throughout (no `any`)
- [ ] Real integration tests passing
- [ ] Lingua CMS analysis works correctly
- [ ] DSL loads in Structurizr Lite without errors
- [ ] Professional-looking diagrams out of the box
- [ ] Performance requirements met
- [ ] Documentation complete

## Current Status

✅ Phase 1.1: Types defined
⏳ Phase 1.2: Implementing enhanced styling system
⏳ Phase 1.3: Integration tests
