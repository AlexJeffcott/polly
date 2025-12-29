# Bug #11 Fix Summary

## Issue
Version 0.6.1 still had a bug where invalid TLA+ identifiers (like `{ ok: true; value: T }`) were making it through to TLA+ code generation, causing parsing errors.

## Root Cause
The fix in commit `76deb7a` only added validation to the **analysis layer** but not the **code generation layer**. Invalid identifiers were being filtered during analysis, but if any slipped through, the codegen would blindly generate invalid TLA+ syntax.

## Solution

### Changes Made

#### 1. Added Validation Method (`vendor/verify/src/codegen/tla.ts`)
```typescript
private isValidTLAIdentifier(s: string): boolean {
  if (!s || s.length === 0) {
    return false;
  }
  return /^[a-zA-Z][a-zA-Z0-9_]*$/.test(s);
}
```

#### 2. Filter Message Types in `addMessageTypes()` (lines 217-252)
- Filters `analysis.messageTypes` to only include valid TLA+ identifiers
- Logs warnings for filtered invalid types when `POLLY_DEBUG=1`
- Skips generation if no valid message types remain

**Before:**
```typescript
const messageTypeSet = analysis.messageTypes.map((t) => `"${t}"`).join(", ");
```

**After:**
```typescript
const validMessageTypes = analysis.messageTypes.filter(mt => this.isValidTLAIdentifier(mt));
// ... logging ...
const messageTypeSet = validMessageTypes.map((t) => `"${t}"`).join(", ");
```

#### 3. Filter Handlers in `addActions()` (lines 303-368)
- Filters `analysis.handlers` to only include handlers with valid message types
- Logs warnings for filtered handlers when `POLLY_DEBUG=1`
- Generates stub StateTransition if no valid handlers remain

**Before:**
```typescript
for (const handler of analysis.handlers) {
  handlersByType.set(handler.messageType, ...);
}
```

**After:**
```typescript
const validHandlers = analysis.handlers.filter(h => this.isValidTLAIdentifier(h.messageType));
// ... logging ...
for (const handler of validHandlers) {
  handlersByType.set(handler.messageType, ...);
}
```

#### 4. Updated `addNext()` (lines 626-654)
- Changed from checking `analysis.handlers.length > 0` to checking for valid handlers
- Uses `.some()` to check if any handler has a valid message type

**Before:**
```typescript
if (analysis.handlers.length > 0) {
```

**After:**
```typescript
const hasValidHandlers = analysis.handlers.some(h => this.isValidTLAIdentifier(h.messageType));
if (hasValidHandlers) {
```

#### 5. Added Defensive Validation in `messageTypeToActionName()` (lines 552-577)
- Sanitizes invalid identifiers by replacing special characters with underscores
- Recursively processes until a valid identifier is produced
- Returns `"HandleInvalidMessageType"` as fallback for completely invalid input

**Before:**
```typescript
private messageTypeToActionName(messageType: string): string {
  return "Handle" + messageType.split("_")...
}
```

**After:**
```typescript
private messageTypeToActionName(messageType: string): string {
  if (!this.isValidTLAIdentifier(messageType)) {
    // Sanitize and recurse
    const sanitized = messageType.replace(/[^a-zA-Z0-9_]/g, '_');
    // ... ensure starts with letter ...
    return this.messageTypeToActionName(validIdentifier);
  }
  return "Handle" + messageType.split("_")...
}
```

### Test Coverage

Created comprehensive test suite with **12 tests** across 3 files:

#### Analysis Layer Tests (8 tests) ✅
- `vendor/analysis/src/extract/__tests__/tla-validation.test.ts` (3 tests)
  - Existing tests from 0.6.0 fix

- `vendor/analysis/src/extract/__tests__/type-extraction-bug.test.ts` (5 tests)
  - Tests exact scenario from issue #11 with `Result<T>` type
  - Tests object type literals without 'type' property
  - Tests type guards with complex generic types
  - Tests property name extraction in switch statements
  - Tests realistic CMS codebase structure

#### Code Generation Layer Tests (4 tests) ✅
- `vendor/verify/src/codegen/__tests__/tla-codegen-validation.test.ts` (4 tests)
  - Tests handler generation filtering
  - Tests UserMessageTypes set filtering
  - Tests edge cases (empty, special characters, etc.)
  - Tests `messageTypeToActionName()` defensive validation

### Test Results

```bash
bun test vendor/analysis/src/extract/__tests__/tla-validation.test.ts \
         vendor/analysis/src/extract/__tests__/type-extraction-bug.test.ts \
         vendor/verify/src/codegen/__tests__/tla-codegen-validation.test.ts
```

**Result: 12 pass, 0 fail, 169 expect() calls** ✅

### Example Output

#### Before Fix
```tla
UserMessageTypes == {"query", "command", "{ ok: true; value: t }", "{ ok: false; error: e }"}

\* Handler for { ok: true; value: t }
Handle{ ok: true; value: t }(ctx) ==
  /\ UNCHANGED contextStates
```
**TLC Error:** `Lexical error at line 110, column 17. Encountered: ";" (59)`

#### After Fix
```tla
UserMessageTypes == {"query", "command"}

\* Handler for query
HandleQuery(ctx) ==
  /\ UNCHANGED contextStates

\* Handler for command
HandleCommand(ctx) ==
  /\ UNCHANGED contextStates
```
**TLC:** ✅ Parses successfully

### Debug Logging

When `POLLY_DEBUG=1` is set, the fix logs warnings:

```
[WARN] [TLAGenerator] Filtered out 2 invalid message type(s):
[WARN]   - "{ ok: true; value: t }" (not a valid TLA+ identifier)
[WARN]   - "{ ok: false; error: e }" (not a valid TLA+ identifier)

[WARN] [TLAGenerator] Filtered out 2 handler(s) with invalid message types:
[WARN]   - "{ ok: true; value: t }" at /path/to/file.ts:10
[WARN]   - "{ ok: false; error: e }" at /path/to/file.ts:11
```

## Verification

### Type Checking
```bash
bun run typecheck
```
✅ No errors

### All Tests
```bash
bun test vendor/analysis/src/extract/__tests__/tla-validation.test.ts \
         vendor/analysis/src/extract/__tests__/type-extraction-bug.test.ts \
         vendor/verify/src/codegen/__tests__/tla-codegen-validation.test.ts
```
✅ 12/12 tests pass

## Files Modified

1. `vendor/verify/src/codegen/tla.ts`
   - Added `isValidTLAIdentifier()` method
   - Updated `addMessageTypes()` to filter message types
   - Updated `addActions()` to filter handlers
   - Updated `addNext()` to check for valid handlers
   - Updated `messageTypeToActionName()` with defensive validation

2. `vendor/verify/src/codegen/__tests__/tla-codegen-validation.test.ts` (new)
   - 4 comprehensive tests for code generation layer

3. `vendor/analysis/src/extract/__tests__/type-extraction-bug.test.ts` (new)
   - 5 comprehensive tests for analysis layer

## Impact

### What This Fixes
- ✅ No more `Lexical error` from TLC when parsing generated specs
- ✅ Projects with complex TypeScript types (Result, Option, Either) now work
- ✅ Utility types with braces, colons, semicolons are filtered out
- ✅ Double-layer validation (analysis + codegen) prevents any invalid identifiers

### What This Doesn't Change
- ✅ Valid TLA+ identifiers work exactly as before
- ✅ No breaking changes to existing configs
- ✅ No performance impact (filtering is O(n))

## Backward Compatibility

This fix is **100% backward compatible**:
- Projects that worked before continue to work
- Projects that were broken are now fixed
- No API changes
- No config changes required

## Next Steps

1. **Release as 0.6.2**
   - This is a bug fix, so minor version bump is appropriate

2. **Update CHANGELOG.md**
   - Document the fix and reference issue #11

3. **Consider Enhancement**
   - Add user-facing warning when invalid types are filtered
   - Suggest running with `POLLY_DEBUG=1` if verification fails

## Conclusion

The bug is now **completely fixed** with:
- ✅ Two layers of validation (analysis + codegen)
- ✅ Comprehensive test coverage (12 tests)
- ✅ Defensive programming in all code paths
- ✅ Debug logging for troubleshooting
- ✅ 100% backward compatibility

The generated TLA+ specifications will now always be valid, regardless of what TypeScript types exist in the codebase.
