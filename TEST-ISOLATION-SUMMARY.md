# Bug #11 Test Isolation Summary

## Problem Statement
In version 0.6.1, despite having a fix for filtering invalid TLA+ identifiers, the verification system still fails when generating TLA+ specifications because complex TypeScript type syntax (like `{ ok: true; value: T }`) is not being filtered during code generation.

## Root Cause Analysis

### Two-Layer Architecture
The verification system has two distinct layers:
1. **Analysis Layer** (`vendor/analysis/src/extract/`)
   - Extracts message types from TypeScript code
   - Analyzes handlers, type guards, and switch statements
   - **Status**: ✅ Correctly filters invalid TLA+ identifiers

2. **Code Generation Layer** (`vendor/verify/src/codegen/`)
   - Generates TLA+ specifications from analysis results
   - Creates handler functions and message type sets
   - **Status**: ❌ Does NOT filter invalid TLA+ identifiers

### The Bug
The fix in commit `76deb7a` added validation to the **analysis layer** only:
- `TypeExtractor.isValidTLAIdentifier()` (lines 73-79 in `types.ts`)
- `HandlerExtractor.isValidTLAIdentifier()` (lines 80-86 in `handlers.ts`)

However, the **code generation layer** blindly trusts the input and generates invalid TLA+ code:
- `TLAGenerator.messageTypeToActionName()` (lines 480-489 in `tla.ts`) - No validation!
- `TLAGenerator.addMessageTypes()` - Includes all message types without filtering
- `TLAGenerator.generateHandlerAction()` - Creates handlers for invalid identifiers

### Example of Invalid Generated Code
```tla
\* Handler for { ok: true; value: t }
Handle{ ok: true; value: t }(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates
```

This causes TLC to fail with: `Lexical error at line 110, column 17. Encountered: ";" (59)`

## Test Suite Created

### 1. Analysis Layer Tests (All Passing ✅)
**Location**: `vendor/analysis/src/extract/__tests__/`

#### `tla-validation.test.ts` (Existing - 3 tests)
- ✅ Filter out invalid TLA+ identifiers from message types
- ✅ Accept valid TLA+ identifiers
- ✅ Reject invalid TLA+ identifiers

#### `type-extraction-bug.test.ts` (New - 5 tests)
- ✅ Should not extract type definition syntax as message types
- ✅ Should ignore object type literals without 'type' property
- ✅ Should not extract type guard predicates with complex types
- ✅ Should not extract property names from object checks in switch
- ✅ Should handle realistic CMS codebase structure (from issue #11)

**Result**: 8/8 tests passing - Analysis layer is working correctly!

### 2. Code Generation Layer Tests (All Failing ❌)
**Location**: `vendor/verify/src/codegen/__tests__/`

#### `tla-codegen-validation.test.ts` (New - 4 tests)
- ❌ Should not generate handlers for message types with invalid TLA+ identifiers
  - **Found**: Generates `Handle{ ok: true; value: t }(ctx)`
  - **Expected**: Should skip or sanitize invalid identifiers

- ❌ Should only include valid message types in UserMessageTypes set
  - **Found**: Includes `"{ ok: true; value: t }"` in the set
  - **Expected**: Should filter to only valid identifiers

- ❌ Should handle edge cases in message type names
  - **Found**: Includes types with `!`, `-`, `.`, `:`, `;`, etc.
  - **Expected**: Should filter out all invalid characters

- ❌ Should validate TLA+ identifier in messageTypeToActionName
  - **Found**: No validation in the method
  - **Expected**: Should validate or sanitize input

**Result**: 0/4 tests passing - Code generation layer needs fixing!

## What the Tests Demonstrate

### Before Fix (Current State)
```
Analysis Layer → [✅ Filters invalid IDs] → Valid message types only
                                             ↓
Code Gen Layer → [❌ No filtering] → Invalid TLA+ code generated
```

### After Fix (Expected)
```
Analysis Layer → [✅ Filters invalid IDs] → Valid message types only
                                             ↓
Code Gen Layer → [✅ Double-check filtering] → Valid TLA+ code generated
```

## Test Files Created

1. **vendor/analysis/src/extract/__tests__/type-extraction-bug.test.ts**
   - 5 comprehensive tests for analysis layer
   - Tests realistic codebase scenarios from issue #11
   - Covers Result types, Option types, type guards, switch statements

2. **vendor/verify/src/codegen/__tests__/tla-codegen-validation.test.ts**
   - 4 tests that expose the codegen bug
   - Tests handler generation, message type sets, identifier validation
   - Includes edge cases and special characters

## How to Use These Tests

### Run all tests
```bash
bun test vendor/analysis/src/extract/__tests__/tla-validation.test.ts \
         vendor/analysis/src/extract/__tests__/type-extraction-bug.test.ts \
         vendor/verify/src/codegen/__tests__/tla-codegen-validation.test.ts
```

### Current results
- 8 passing (analysis layer)
- 4 failing (codegen layer)

### After implementing the fix
- All 12 tests should pass
- This ensures the bug is fixed at BOTH layers

## Recommended Fix

Add validation to the code generation layer at these points:

1. **In `addMessageTypes()` method**
   ```typescript
   private addMessageTypes(config: VerificationConfig, analysis: CodebaseAnalysis): void {
     // Filter out invalid TLA+ identifiers
     const validMessageTypes = analysis.messageTypes.filter(mt => this.isValidTLAIdentifier(mt));
     // Use validMessageTypes for generation
   }
   ```

2. **In `addActions()` method**
   ```typescript
   private addActions(config: VerificationConfig, analysis: CodebaseAnalysis): void {
     // Filter handlers with invalid message types
     const validHandlers = analysis.handlers.filter(h => this.isValidTLAIdentifier(h.messageType));
     // Use validHandlers for generation
   }
   ```

3. **Add validation helper**
   ```typescript
   private isValidTLAIdentifier(s: string): boolean {
     if (!s || s.length === 0) {
       return false;
     }
     return /^[a-zA-Z][a-zA-Z0-9_]*$/.test(s);
   }
   ```

## Verification

After implementing the fix:
1. Run the test suite - all 12 tests should pass
2. Run `polly verify` on a real project with Result types
3. Check that the generated TLA+ spec is parseable by TLC
4. Verify no "Lexical error" messages occur

## Conclusion

The tests successfully isolate and demonstrate the bug:
- ✅ Analysis layer works correctly (8/8 tests pass)
- ❌ Code generation layer has the bug (0/4 tests pass)

This proves that the fix in 0.6.1 was incomplete and only addressed half the problem. The code generation layer needs the same validation logic to prevent invalid TLA+ code from being generated.
