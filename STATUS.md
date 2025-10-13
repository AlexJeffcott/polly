# Project Status and Next Steps

## Current Status

### ✅ Completed: Verification System Foundation

A complete type-driven TLA+ verification system with comment-driven configuration.

**Working Components:**

1. **Type Extraction** ✅
   - Parses TypeScript AST with ts-morph
   - Detects all primitive types (boolean, string, number, enum)
   - Handles complex types (arrays, Map, Set)
   - Properly detects nullable types (`T | null`)
   - Filters intermediate objects (leaf-only fields)
   - Assigns confidence levels (high/medium/low)

2. **Config Generation** ✅
   - Smart comments based on confidence
   - Type-specific guidance
   - `/* CONFIGURE */` markers for validation
   - Nullable field notes
   - Examples and suggestions

3. **Config Validation** ✅
   - Detects incomplete configuration
   - Finds `/* CONFIGURE */` markers
   - Validates bounds (min/max, lengths, sizes)
   - Warns about unrealistic values
   - Clear error messages with suggestions

4. **TLA+ Generation** ✅
   - Converts config → TLA+ spec
   - Maps TypeScript types → TLA+ types
   - Generates State type definition
   - Creates initial state with defaults
   - Generates `.cfg` file with constants

5. **Docker Integration** ✅
   - Docker availability check
   - TLA+ image management
   - TLC execution with timeout/workers
   - Output parsing (success/violations/errors)
   - Error trace extraction

6. **CLI Interface** ✅
   - `bun verify --setup` - Generate config
   - `bun verify --validate` - Check config
   - `bun verify` - Run verification
   - Color-coded output
   - Progress indicators

### 📁 Project Structure

```
/Users/AJT/web-ext/
├── specs/
│   ├── tla/
│   │   ├── MessageRouter.tla        # Base message routing spec
│   │   ├── MessageRouter.cfg
│   │   └── README.md
│   ├── Dockerfile                    # TLA+ Docker container
│   └── docker-compose.yml
├── packages/
│   ├── verify/                       # NEW: Verification system
│   │   ├── src/
│   │   │   ├── extract/types.ts     # Type extraction
│   │   │   ├── codegen/
│   │   │   │   ├── config.ts        # Config generator
│   │   │   │   └── tla.ts           # TLA+ generator
│   │   │   ├── config/parser.ts     # Validator
│   │   │   ├── runner/docker.ts     # Docker runner
│   │   │   ├── primitives/index.ts  # API (stubs)
│   │   │   ├── cli.ts               # CLI
│   │   │   └── types.ts             # Core types
│   │   ├── examples/
│   │   │   ├── state.ts
│   │   │   ├── verification.config.ts
│   │   │   └── generated/
│   │   │       ├── UserApp.tla
│   │   │       └── UserApp.cfg
│   │   ├── README.md
│   │   ├── IMPLEMENTATION.md
│   │   └── package.json
│   ├── web-ext/                      # Main framework
│   │   └── src/
│   │       ├── background/
│   │       │   └── message-router.ts
│   │       └── shared/
│   │           └── lib/message-bus.ts
│   └── tests/                        # Test package
└── package.json
```

### 🎯 What Works Right Now

**User can:**
1. Run `bun verify --setup` to analyze codebase and generate config
2. Fill in marked fields in `specs/verification.config.ts`
3. Run `bun verify --validate` to check completeness
4. Run `bun verify` to generate TLA+ spec and run TLC

**System generates:**
- Complete State type definition with bounds
- Initial state with sensible defaults
- Basic invariants (TypeOK, NoRoutingLoops, StateTypeInvariant)
- TLC configuration with all constants

### ✅ Recent Progress (Phase 1)

**Message Routing Integration:**
1. ✅ TLA+ generator now EXTENDS MessageRouter (not redefines)
2. ✅ Message type constants generated from extracted types
3. ✅ Application state (contextStates) properly added
4. ✅ UserInit extends MessageRouter's Init
5. ✅ UserNext extends MessageRouter's Next
6. ✅ Base spec automatically copied to generated directory

**Generated spec now includes:**
- Full message routing from MessageRouter (Connect/Disconnect/Send/Route/Timeout/Broadcast)
- Application-specific State type definition
- Per-context state tracking (contextStates variable)
- State type invariant checking

### ⚠️ Current Limitations

**What's NOT working yet:**

1. **State Transitions from Messages** 🔴
   - StateTransition action is a stub (doesn't modify state)
   - Need to extract message handlers from code
   - Need to generate state update actions based on handlers
   - Users can't verify "when USER_LOGIN, set loggedIn=true"

2. **Primitives API** 🔴
   - `before()`, `requires()`, `ensures()` defined but not translated
   - No TLA+ generation from primitive calls
   - Users can't express custom invariants easily

3. **Full Verification Testing** 🟡
   - Generated spec extends MessageRouter correctly
   - But state transitions are stubbed out
   - Need real test with Docker to verify it works end-to-end

## Next Steps (Priority Order)

### 🚀 Phase 1: Complete Message Routing (HIGH PRIORITY) - MOSTLY DONE ✅

Make the generated spec actually verify message routing behavior.

**Tasks:**
1. ✅ Extend TLA+ generator to include message routing actions
2. ✅ Integrate with base MessageRouter.tla spec (import/extend)
3. ✅ Generate message type constants from extracted types
4. ✅ Copy base spec to generated directory for TLC
5. ⏳ Test end-to-end with Docker (next step)

**Progress:** 80% complete - spec generation works, need to test with TLC

**Remaining:** Run actual verification with Docker to ensure TLC can parse and check the spec

### 🎨 Phase 2: Handler Extraction (MEDIUM PRIORITY)

Extract state mutations from message handlers in code.

**Tasks:**
1. Parse message handler functions (`.on("MESSAGE_TYPE", handler)`)
2. Detect state assignments (`state.field = value`)
3. Generate TLA+ state transition actions
4. Connect message types → state changes in spec

**Why:** Enables verification of state consistency across contexts

**Estimated:** 6-8 hours

### 🔧 Phase 3: Primitives Implementation (MEDIUM PRIORITY)

Translate high-level API → TLA+ invariants.

**Tasks:**
1. Implement `before()` → temporal ordering invariant
2. Implement `requires()` → precondition check
3. Implement `ensures()` → postcondition check
4. Implement `never.concurrent()` → mutual exclusion
5. Implement `eventually.delivers()` → liveness property

**Why:** Makes it easy for users to express correctness properties

**Estimated:** 4-5 hours

### 📊 Phase 4: Better Message Type Integration (LOW PRIORITY)

Use extracted message types in spec generation.

**Tasks:**
1. Extract message types from TypeScript unions
2. Generate message type constants in TLA+
3. Use in SendMessage/RouteMessage actions
4. Validate message types in routing

**Why:** Type safety, catches message routing to wrong targets

**Estimated:** 2-3 hours

### 🎯 Phase 5: Polish & DX (LOW PRIORITY)

Improve user experience.

**Tasks:**
1. Watch mode - re-verify on file changes
2. Better violation traces - map to TypeScript concepts
3. Interactive setup mode (CLI wizard)
4. Caching for faster incremental verification
5. Documentation with real examples

**Why:** Makes the system production-ready

**Estimated:** 6-8 hours

## Immediate Next Action

**Start with Phase 1: Complete Message Routing**

This is the most impactful - it turns the system from "generates a spec" to "actually verifies message routing".

**Concrete first task:**
1. Update TLA+ generator to extend MessageRouter base spec
2. Generate message type constants from extracted types
3. Add SendMessage/RouteMessage actions to generated spec
4. Test with simple message flow

**Success criteria:**
- Generated spec includes full message routing
- Can verify "message from popup to background gets delivered"
- Can catch routing loops
- Can verify message ordering

## Long-Term Vision

**End state:** Users define types and invariants in TypeScript, system verifies automatically.

```typescript
// types/state.ts
export type AppState = { /* ... */ }

// specs/invariants.ts
export const invariants = [
  before("USER_LOGIN", "SYNC_TODOS"),
  requires("SYNC_TODOS", (s) => s.user.loggedIn),
  ensures("USER_LOGOUT", (s) => s.user.loggedIn === false)
]

// Build runs verification automatically
$ bun build:prod
✓ Types checked
✓ Verification passed (1,234 states explored)
✓ Build complete
```

**Value proposition:**
- Formal verification with zero TLA+ knowledge required
- Catches concurrency bugs before production
- No test writing for message routing behavior
- Documentation that's verified to be correct

## Questions to Answer

1. **Should verification be opt-in or opt-out?**
   - Current: Opt-in (need to enable in config)
   - Could be: Always on, but only warn in dev

2. **How to handle verification failures in CI?**
   - Block builds? Just warn? Configurable?

3. **What's the right balance of bounds?**
   - Small (fast, may miss bugs) vs Large (thorough, slow)
   - Presets? Auto-adjust based on app size?

4. **Should we extract invariants from tests?**
   - Look at existing test assertions
   - Convert to TLA+ invariants automatically
   - "Your tests, formally verified"

## Success Metrics

**System is successful if:**
1. ✅ Users can set it up in <5 minutes (mostly done)
2. ⏳ It catches a real bug in message routing (need Phase 1)
3. ⏳ Verification runs in <30s for typical app (need optimization)
4. ⏳ 90% of configuration is auto-generated (currently ~60%)
5. ⏳ Users understand violations without TLA+ knowledge (need better traces)

## Resources

- **Specs:** `/Users/AJT/web-ext/specs/tla/`
- **Package:** `/Users/AJT/web-ext/packages/verify/`
- **Examples:** `/Users/AJT/web-ext/packages/verify/examples/`
- **Docs:**
  - `/Users/AJT/web-ext/packages/verify/README.md`
  - `/Users/AJT/web-ext/packages/verify/IMPLEMENTATION.md`

## Summary

**We have:** A complete foundation that extracts types, generates config, validates, and runs TLC.

**We need:** Message routing actions and primitives translation to make it actually useful.

**Next:** Implement Phase 1 (message routing) to enable real verification.
