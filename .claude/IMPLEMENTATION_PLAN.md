# Implementation Plan: Expose Tier 1 & 2 Optimization Features

## Problem Summary

Issue #13 reports that `polly verify --optimize` recommends configuration options that aren't accessible to users:
- `messages.perType` (per-message-type concurrency limits)
- `messages.exclude/include` (message filtering)
- `messages.symmetry` (symmetry reduction)
- `verification.*` options (timeout, workers)
- `tier2.temporalConstraints` (ordering requirements)
- `tier2.boundedExploration` (depth limits)

## Root Cause Analysis

After thorough codebase exploration, I've discovered:

**✅ GOOD NEWS: Features ARE Already Implemented!**
- TLA+ generator (`tools/verify/src/codegen/tla.ts`) fully supports all Tier 1 & 2 optimizations
- Internal types (`tools/verify/src/types.ts`) define all the configuration options
- Lines 735-747: `include`/`exclude` filtering
- Lines 774-817: `symmetry` reduction
- Lines 416-422: `perMessageBounds`
- Lines 1883-1980: Tier 2 `temporalConstraints` and `boundedExploration`

**❌ THE ACTUAL PROBLEM: Features NOT Exposed to Users**
- Exported config types (`tools/verify/src/config.ts`) only expose `maxInFlight` and `maxTabs`
- The `LegacyVerificationConfig` interface uses `[key: string]: unknown` which allows users to add these fields, but:
  - No TypeScript autocompletion
  - No validation
  - No documentation
  - Users don't know these features exist!

## Solution: Expose Existing Features

Rather than implementing new features, we need to **expose the already-implemented features** to users.

## Implementation Steps

### Step 1: Update Exported Config Types
**File:** `/tools/verify/src/config.ts`

Current interface (limited):
```typescript
interface LegacyVerificationConfig {
  state: Record<string, unknown>;
  messages: {
    maxInFlight?: number;
    maxTabs?: number;
    [key: string]: unknown;  // Allows anything but no types!
  };
  onBuild?: "warn" | "error" | "off";
}
```

Update to match internal types:
```typescript
interface LegacyVerificationConfig {
  state: Record<string, unknown>;
  messages: {
    // Existing bounds
    maxInFlight?: number;
    maxTabs?: number;
    maxClients?: number;
    maxRenderers?: number;
    maxWorkers?: number;
    maxContexts?: number;

    // Tier 1 Optimizations (no precision loss)
    include?: string[];
    exclude?: string[];
    symmetry?: string[][];
    perMessageBounds?: Record<string, number>;
  };
  onBuild?: "warn" | "error" | "off";
  onRelease?: "warn" | "error" | "off";
  preset?: "quick" | "balanced" | "thorough";

  // Verification engine options
  verification?: {
    timeout?: number;
    workers?: number;
  };

  // Tier 2 Optimizations (controlled approximations)
  tier2?: {
    temporalConstraints?: Array<{
      before: string;
      after: string;
      description?: string;
    }>;
    boundedExploration?: {
      maxDepth?: number;
      criticalPaths?: string[][];
    };
  };
}
```

**Key Changes:**
- Add all project-specific bounds (maxClients, maxRenderers, etc.)
- Add Tier 1 optimization fields
- Add `verification` section
- Add `tier2` section
- Add `onRelease` and `preset` (missing from current interface)
- Remove `[key: string]: unknown` from messages - we now have proper types

### Step 2: Update Config Validation
**File:** `/tools/verify/src/config/parser.ts`

Add validation for new fields in the `validateConfig()` method:

```typescript
private validateConfig(config: VerificationConfig): void {
  // Existing validation
  this.findNullPlaceholders(config.state, "state");
  this.findNullPlaceholders(config.messages, "messages");
  this.validateMessageBounds(config.messages);

  // NEW: Validate Tier 1 optimizations
  this.validateTier1Optimizations(config.messages);

  // NEW: Validate verification options
  if (config.verification) {
    this.validateVerificationOptions(config.verification);
  }

  // NEW: Validate Tier 2 optimizations
  if (config.tier2) {
    this.validateTier2Optimizations(config.tier2);
  }
}
```

Add new validation methods:

```typescript
private validateTier1Optimizations(messages: MessageConfig): void {
  // Validate include/exclude are mutually exclusive
  if (messages.include && messages.exclude) {
    this.issues.push({
      type: "invalid_value",
      severity: "error",
      field: "messages",
      message: "Cannot use both 'include' and 'exclude' filters",
      suggestion: "Use either 'include' OR 'exclude', not both"
    });
  }

  // Validate symmetry groups have at least 2 members
  if (messages.symmetry) {
    for (const group of messages.symmetry) {
      if (group.length < 2) {
        this.issues.push({
          type: "invalid_value",
          severity: "warning",
          field: "messages.symmetry",
          message: "Symmetry group must have at least 2 message types",
          suggestion: "Remove single-element symmetry groups"
        });
      }
    }
  }

  // Validate perMessageBounds values are realistic
  if (messages.perMessageBounds) {
    for (const [msgType, bound] of Object.entries(messages.perMessageBounds)) {
      if (bound < 1 || bound > 20) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: `messages.perMessageBounds.${msgType}`,
          message: `Per-message bound ${bound} is outside recommended range (1-20)`,
          suggestion: "Consider adjusting bound to a more realistic value"
        });
      }
    }
  }
}

private validateVerificationOptions(verification: NonNullable<VerificationConfig["verification"]>): void {
  if (verification.timeout !== undefined) {
    if (verification.timeout < 0) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        field: "verification.timeout",
        message: "Timeout cannot be negative",
        suggestion: "Use 0 for no timeout, or positive number for timeout in seconds"
      });
    }
    if (verification.timeout > 3600) {
      this.issues.push({
        type: "unrealistic_bound",
        severity: "warning",
        field: "verification.timeout",
        message: "Timeout over 1 hour (3600s) is very long",
        suggestion: "Consider reducing timeout or using 0 for no limit"
      });
    }
  }

  if (verification.workers !== undefined) {
    if (verification.workers < 1) {
      this.issues.push({
        type: "invalid_value",
        severity: "error",
        field: "verification.workers",
        message: "Workers must be at least 1",
        suggestion: "Use 1 or more workers"
      });
    }
    if (verification.workers > 16) {
      this.issues.push({
        type: "unrealistic_bound",
        severity: "warning",
        field: "verification.workers",
        message: "More than 16 workers may not improve performance",
        suggestion: "Typical range is 1-8 workers"
      });
    }
  }
}

private validateTier2Optimizations(tier2: NonNullable<VerificationConfig["tier2"]>): void {
  // Validate temporal constraints
  if (tier2.temporalConstraints) {
    for (const constraint of tier2.temporalConstraints) {
      if (!constraint.before || !constraint.after) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "tier2.temporalConstraints",
          message: "Temporal constraint must have 'before' and 'after' fields",
          suggestion: "Specify both message types for ordering constraint"
        });
      }
      if (constraint.before === constraint.after) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "tier2.temporalConstraints",
          message: "Temporal constraint cannot have same message type for 'before' and 'after'",
          suggestion: "Use different message types"
        });
      }
    }
  }

  // Validate bounded exploration
  if (tier2.boundedExploration) {
    if (tier2.boundedExploration.maxDepth !== undefined) {
      if (tier2.boundedExploration.maxDepth < 1) {
        this.issues.push({
          type: "invalid_value",
          severity: "error",
          field: "tier2.boundedExploration.maxDepth",
          message: "maxDepth must be at least 1",
          suggestion: "Use positive integer for depth limit"
        });
      }
      if (tier2.boundedExploration.maxDepth > 100) {
        this.issues.push({
          type: "unrealistic_bound",
          severity: "warning",
          field: "tier2.boundedExploration.maxDepth",
          message: "maxDepth > 100 may not be useful",
          suggestion: "Typical range is 10-50"
        });
      }
    }
  }
}
```

### Step 3: Update Config Generation Templates
**File:** `/tools/verify/src/codegen/config.ts`

The config generator should add comments explaining Tier 1 & 2 options:

```typescript
private generateMessagesConfig(): void {
  this.line("messages: {");
  this.indent++;

  // Existing bounds
  this.line(`maxInFlight: ${this.defaultMaxInFlight},`);
  if (this.projectType === "chrome-extension") {
    this.line("maxTabs: 1,");
  }

  // Add commented-out Tier 1 optimization examples
  this.line("");
  this.line("// ─────────────────────────────────────────────────────────");
  this.line("// Tier 1 Optimizations (no precision loss)");
  this.line("// ─────────────────────────────────────────────────────────");
  this.line("// Uncomment and configure as needed:");
  this.line("//");
  this.line("// Filter messages (include OR exclude, not both):");
  this.line("// include: ['authenticate', 'query', 'command'],");
  this.line("// exclude: ['load', 'unload', 'resize', 'scroll'],");
  this.line("//");
  this.line("// Symmetry reduction (group equivalent message types):");
  this.line("// symmetry: [");
  this.line("//   ['query_user', 'query_post'],  // All query types are symmetric");
  this.line("//   ['create', 'update', 'delete'], // CRUD operations are symmetric");
  this.line("// ],");
  this.line("//");
  this.line("// Per-message bounds (different maxInFlight per type):");
  this.line("// perMessageBounds: {");
  this.line("//   'authenticate': 1,  // Sequential authentication");
  this.line("//   'query': 5,         // Allow more concurrent queries");
  this.line("// },");

  this.indent--;
  this.line("},");
}

private generateTier2Section(): void {
  this.line("");
  this.line("// ─────────────────────────────────────────────────────────");
  this.line("// Tier 2 Optimizations (controlled approximations)");
  this.line("// ─────────────────────────────────────────────────────────");
  this.line("// Use with caution - these reduce precision for performance");
  this.line("//");
  this.line("// tier2: {");
  this.line("//   temporalConstraints: [");
  this.line("//     { before: 'LOGIN', after: 'LOGOUT', description: 'Must login before logout' },");
  this.line("//   ],");
  this.line("//   boundedExploration: {");
  this.line("//     maxDepth: 20,  // Limit exploration depth");
  this.line("//   },");
  this.line("// },");
}
```

### Step 4: Update Type Definitions Package Export
**File:** `/tools/verify/src/types.ts`

Already has the right types! Just need to make sure they're exported properly and match the config.ts interface.

### Step 5: Add Documentation to Optimization Prompt
**File:** `/tools/teach/src/system-prompt.ts`

The optimization prompt already mentions these features! We just need to ensure it knows they're NOW accessible:

```typescript
const optimizationGuidance = `
## Available Optimization Features (v0.9.0+)

You can now recommend ALL Tier 1 and Tier 2 optimizations - they are fully implemented!

### Tier 1: Safe Optimizations (Zero Precision Loss)

1. **Message Filtering** - Use \`include\` or \`exclude\`
2. **Symmetry Reduction** - Use \`symmetry\` groups
3. **Per-Message Bounds** - Use \`perMessageBounds\`

### Tier 2: Controlled Approximations

1. **Temporal Constraints** - Use \`tier2.temporalConstraints\`
2. **Bounded Exploration** - Use \`tier2.boundedExploration\`

All features have full TypeScript support with validation!
`;
```

### Step 6: Add Tests
**File:** `/tools/verify/src/config/parser.test.ts` (create if doesn't exist)

Add tests for validation logic:
- Test include/exclude mutual exclusivity
- Test symmetry group validation
- Test perMessageBounds range validation
- Test temporal constraints validation
- Test bounded exploration validation

## Files to Modify

1. ✏️ `/tools/verify/src/config.ts` - Update exported type definitions
2. ✏️ `/tools/verify/src/config/parser.ts` - Add validation for new fields
3. ✏️ `/tools/verify/src/codegen/config.ts` - Add commented examples in generated config
4. ✏️ `/tools/teach/src/system-prompt.ts` - Update optimization guidance
5. ✅ `/tools/verify/src/types.ts` - Already correct, no changes needed
6. ✅ `/tools/verify/src/codegen/tla.ts` - Already implements everything, no changes needed
7. 📝 `/tools/verify/src/config/parser.test.ts` - Add tests (new file)

## Testing Strategy

1. **Unit Tests**
   - Validation logic for each new field
   - Edge cases (empty arrays, invalid values)

2. **Integration Tests**
   - Generate config with new features
   - Validate config passes validation
   - Generate TLA+ spec successfully
   - Run TLC model checker

3. **End-to-End Test**
   - Create test project
   - Run `polly verify --optimize`
   - Apply recommendations
   - Verify it works without errors

## Backwards Compatibility

✅ **Fully Backwards Compatible**
- All new fields are optional
- Existing configs will continue to work
- No breaking changes to config structure
- Legacy configs will be upgraded automatically

## Documentation Updates

After implementation, update:
1. README.md - Document new optimization features
2. CHANGELOG.md - Add entry for v0.9.0
3. Examples directory - Add example configs with optimizations

## Version Bump

This is a minor version bump: **v0.8.0 → v0.9.0**
- Adds new features
- No breaking changes
- Backwards compatible

## Success Criteria

✅ Users can access all Tier 1 & 2 optimization features with TypeScript autocomplete
✅ Config validation catches invalid configurations
✅ Generated configs include helpful comments about optimizations
✅ `polly verify --optimize` recommendations work without errors
✅ All tests pass
✅ Issue #13 is resolved
