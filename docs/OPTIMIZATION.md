# Verification Optimization Guide

This guide explains how to optimize Polly's formal verification performance using Tier 1 and Tier 2 optimization strategies.

## Overview

Polly uses TLA+ and TLC model checking to formally verify message-passing systems. As your application grows, the state space can become very large, making verification slow or infeasible. This guide shows you how to reduce the state space by 90-95% while maintaining correctness guarantees.

## Quick Start

```bash
# Get AI-powered optimization suggestions
polly verify --optimize

# Or manually configure optimizations in specs/verification.config.ts
```

## Optimization Tiers

### Tier 1: Zero Precision Loss

These optimizations reduce the state space without losing any verification coverage. They're safe to use in all scenarios.

### Tier 2: Controlled Approximations

These optimizations make controlled trade-offs, limiting exploration depth or enforcing known constraints. Use when Tier 1 alone isn't sufficient.

---

## Tier 1 Optimizations

### 1. Message Type Filtering

**Impact**: Can reduce message types by 80-90%

**Problem**: Your application may register many message types, but not all are relevant for verification. Browser events, UI notifications, and debug messages often don't affect core business logic.

**Solution**: Use `include` or `exclude` to filter message types.

**Configuration**:

```typescript
export default defineVerification({
  messages: {
    maxInFlight: 3,

    // Option A: Include only specific types
    include: [
      'USER_LOGIN',
      'USER_LOGOUT',
      'BOOKMARK_ADD',
      'BOOKMARK_REMOVE',
      'SETTINGS_UPDATE',
    ],

    // Option B: Exclude specific types (don't use both!)
    exclude: [
      'UI_NOTIFICATION',
      'DEBUG_LOG',
      'ANALYTICS_TRACK',
    ],
  },
});
```

**When to use**:
- Your app has many message types but only a subset affects critical state
- You want to focus verification on specific workflows (e.g., authentication flow)
- You're debugging a specific feature and want faster iteration

**Example Results**:
```
[INFO] Message filtering (include): 43 → 7 message types (83.7% reduction)
```

**Reference**: See [Issue #12](https://github.com/fairfoxai/polly/issues/12) for the original feature request.

---

### 2. Symmetry Reduction

**Impact**: TLC can reduce state space by 2-10x depending on symmetry

**Problem**: Some message types behave identically. For example, if you have three worker threads that all do the same thing, swapping `WORKER1_TASK` and `WORKER2_TASK` in any state produces equivalent behavior.

**Solution**: Group interchangeable message types so TLC treats them as symmetric.

**Configuration**:

```typescript
export default defineVerification({
  messages: {
    maxInFlight: 3,

    // Groups of message types where order doesn't affect properties
    symmetry: [
      ['WORKER1_TASK', 'WORKER2_TASK', 'WORKER3_TASK'],
      ['REPLICA1_SYNC', 'REPLICA2_SYNC'],
    ],
  },
});
```

**Generated TLA+**:
```tla
SymmetrySet1 == {"WORKER1_TASK", "WORKER2_TASK", "WORKER3_TASK"}
SymmetrySet2 == {"REPLICA1_SYNC", "REPLICA2_SYNC"}

SYMMETRY SymmetrySet1
SYMMETRY SymmetrySet2
```

**When to use**:
- You have multiple workers, replicas, or shards that behave identically
- Message types differ only in their ID but have identical semantics
- You want TLC to explore fewer equivalent states

**Important**: Only group message types that are truly interchangeable. If their handlers differ in any way, don't group them.

---

### 3. Per-Message Bounds

**Impact**: Reduces states by 50-80% by modeling realistic concurrency

**Problem**: Setting `maxInFlight: 5` means TLC explores scenarios where any 5 messages are in-flight simultaneously. But in reality, some operations are always sequential (like authentication), while others can be concurrent (like read queries).

**Solution**: Set different concurrency limits per message type to match real-world behavior.

**Configuration**:

```typescript
export default defineVerification({
  messages: {
    maxInFlight: 3,  // Global default

    // Override per message type
    perMessageBounds: {
      'USER_LOGIN': 1,         // Authentication is always sequential
      'USER_LOGOUT': 1,        // Logout is sequential
      'BOOKMARK_ADD': 2,       // Allow some bookmark concurrency
      'BOOKMARK_REMOVE': 2,    // Allow some bookmark concurrency
      'SETTINGS_UPDATE': 1,    // Settings updates are sequential
      'TAB_GET_CURRENT': 3,    // Tab queries can be highly concurrent
    },
  },
});
```

**Generated TLA+ Constants**:
```tla
CONSTANTS
  MaxMessages = 3
  MaxMessages_USER_LOGIN = 1
  MaxMessages_USER_LOGOUT = 1
  MaxMessages_BOOKMARK_ADD = 2
  MaxMessages_BOOKMARK_REMOVE = 2
  MaxMessages_SETTINGS_UPDATE = 1
  MaxMessages_TAB_GET_CURRENT = 3
```

**Generated TLA+ Constraint**:
```tla
StateConstraint ==
  /\ Len(messages) <= MaxMessages
  /\ Cardinality({m \in DOMAIN messages : messages[m].type = "USER_LOGIN"}) <= MaxMessages_USER_LOGIN
  /\ Cardinality({m \in DOMAIN messages : messages[m].type = "USER_LOGOUT"}) <= MaxMessages_USER_LOGOUT
  /\ Cardinality({m \in DOMAIN messages : messages[m].type = "BOOKMARK_ADD"}) <= MaxMessages_BOOKMARK_ADD
  ...
```

**When to use**:
- Different operations in your system have different concurrency characteristics
- You want to model realistic scenarios without over-exploration
- You know certain operations are always serialized (like writes to a single resource)

**How to choose bounds**:
1. Authentication/authorization: Usually 1 (sequential)
2. Write operations: 1-2 (often serialized or low concurrency)
3. Read operations: 2-5 (can be highly concurrent)
4. Background tasks: Match your actual worker pool size

---

## Tier 2 Optimizations

Use these when Tier 1 optimizations aren't sufficient. They make controlled trade-offs.

### 1. Temporal Constraints

**Impact**: Eliminates invalid state sequences, reducing exploration by 30-60%

**Problem**: TLC explores all possible message orderings, including impossible ones. For example, it explores states where `USER_LOGOUT` happens before `USER_LOGIN`, which can't happen in reality.

**Solution**: Declare ordering requirements between message types to prune impossible sequences.

**Configuration**:

```typescript
export default defineVerification({
  tier2: {
    temporalConstraints: [
      {
        before: 'USER_LOGIN',
        after: 'USER_LOGOUT',
        description: 'Must login before logout'
      },
      {
        before: 'USER_LOGIN',
        after: 'BOOKMARK_ADD',
        description: 'Must be logged in to add bookmarks'
      },
      {
        before: 'USER_LOGIN',
        after: 'SETTINGS_UPDATE',
        description: 'Must be logged in to update settings'
      },
    ],
  },
});
```

**Generated TLA+ Invariants**:
```tla
\* Tier 2: Temporal constraint invariants
\* Enforce ordering requirements between message types

\* Must login before logout
TemporalConstraint1 ==
  \* If USER_LOGOUT has been delivered, then USER_LOGIN must have been delivered
  (\E m \in DOMAIN delivered : delivered[m].type = "USER_LOGOUT")
  =>
  (\E m \in DOMAIN delivered : delivered[m].type = "USER_LOGIN")

\* Must be logged in to add bookmarks
TemporalConstraint2 ==
  (\E m \in DOMAIN delivered : delivered[m].type = "BOOKMARK_ADD")
  =>
  (\E m \in DOMAIN delivered : delivered[m].type = "USER_LOGIN")
```

**When to use**:
- Your application has clear ordering requirements (authentication flows, state machines)
- You want to focus verification on valid workflows
- Impossible orderings are cluttering your state space

**Trade-off**: If your constraint is wrong (e.g., there's an edge case where logout can happen without login), you won't catch bugs in that scenario. Only use constraints you're certain about.

**How to identify constraints**:
1. Authentication/authorization flows (login before protected operations)
2. State machine transitions (open before close, create before delete)
3. Setup before use (initialize before read/write)

---

### 2. Bounded Exploration

**Impact**: Limits state depth, making verification complete in finite time

**Problem**: Complex systems can have very deep state spaces. TLC might explore millions of states without completing.

**Solution**: Set a maximum exploration depth to bound verification time.

**Configuration**:

```typescript
export default defineVerification({
  tier2: {
    boundedExploration: {
      maxDepth: 15,  // Limit to 15 state transitions from initial state
    },
  },
});
```

**Generated TLA+ Constraint**:
```tla
StateConstraint ==
  /\ Len(messages) <= MaxMessages
  /\ TLCGet("level") <= 15  \* Tier 2: Bounded exploration
```

**When to use**:
- Verification is taking too long even with Tier 1 optimizations
- You want to verify "shallow" properties (bugs that manifest quickly)
- You're doing iterative development and want fast feedback

**Trade-off**: You won't explore states deeper than maxDepth, so bugs that only appear after many transitions won't be found.

**How to choose maxDepth**:
- Start with 10-15 for fast iteration
- Increase to 20-30 for thorough verification
- Use 50+ if you have the time and need deep exploration

**Future feature**: Critical paths (not yet implemented)
```typescript
boundedExploration: {
  maxDepth: 15,
  criticalPaths: [
    ['USER_LOGIN', 'BOOKMARK_ADD', 'USER_LOGOUT'],
    ['USER_LOGIN', 'SETTINGS_UPDATE', 'USER_LOGOUT'],
  ],
}
```
This would ensure specific sequences are always explored even at depth > maxDepth.

---

## Complete Example

Here's a real-world example combining all optimizations:

```typescript
// specs/verification.config.ts
import { defineVerification } from "@fairfox/polly/verify";

export default defineVerification({
  state: {},

  messages: {
    maxInFlight: 3,
    maxTabs: 1,

    // ══════════════════════════════════════════════════════════
    // TIER 1 OPTIMIZATIONS (Zero precision loss)
    // ══════════════════════════════════════════════════════════

    // 1. Message Type Filtering
    // Focus on authentication and bookmark management flows
    include: [
      'USER_LOGIN',
      'USER_LOGOUT',
      'BOOKMARK_ADD',
      'BOOKMARK_REMOVE',
      'SETTINGS_GET',
      'SETTINGS_UPDATE',
      'TAB_GET_CURRENT',
    ],

    // 2. Symmetry Reduction
    // (No symmetric message types in this example)
    symmetry: [],

    // 3. Per-Message Bounds
    // Model realistic concurrency for each operation
    perMessageBounds: {
      'USER_LOGIN': 1,        // Auth is sequential
      'USER_LOGOUT': 1,       // Logout is sequential
      'BOOKMARK_ADD': 2,      // Allow some bookmark concurrency
      'BOOKMARK_REMOVE': 2,   // Allow some bookmark concurrency
      'SETTINGS_UPDATE': 1,   // Settings updates are sequential
      'TAB_GET_CURRENT': 3,   // Tab queries are highly concurrent
    },
  },

  // ══════════════════════════════════════════════════════════
  // TIER 2 OPTIMIZATIONS (Controlled approximations)
  // ══════════════════════════════════════════════════════════

  tier2: {
    // 1. Temporal Constraints
    // Enforce known ordering requirements
    temporalConstraints: [
      {
        before: 'USER_LOGIN',
        after: 'USER_LOGOUT',
        description: 'Must login before logout'
      },
      {
        before: 'USER_LOGIN',
        after: 'BOOKMARK_ADD',
        description: 'Must be logged in to add bookmarks'
      },
      {
        before: 'USER_LOGIN',
        after: 'SETTINGS_UPDATE',
        description: 'Must be logged in to update settings'
      },
    ],

    // 2. Bounded Exploration
    // Limit depth for fast verification
    boundedExploration: {
      maxDepth: 15,
    },
  },

  onBuild: 'warn',
  onRelease: 'error',
});
```

**Results**:
```
[INFO] Message filtering (include): 43 → 7 message types (83.7% reduction)
```

**Combined Impact**: ~90-95% state space reduction while maintaining verification of critical properties.

---

## Using `polly verify --optimize`

Polly includes an AI-powered optimization assistant that analyzes your project and suggests specific optimizations.

**Usage**:

```bash
# Set your Claude API key
export ANTHROPIC_API_KEY=your_key_here

# Start optimization session
polly verify --optimize
```

**The assistant will**:
1. Analyze your codebase and message types
2. Review your current verification configuration
3. Suggest specific Tier 1 and Tier 2 optimizations
4. Explain the trade-offs for each suggestion
5. Help you implement and test the optimizations

**Example interaction**:
```
> I see you have 43 message types but only 7 are related to user authentication
> and bookmark management. Consider using message filtering:
>
>   include: ['USER_LOGIN', 'USER_LOGOUT', 'BOOKMARK_ADD', ...]
>
> This would reduce your state space by ~83% with zero precision loss.
```

---

## Performance Impact

Here are typical results from applying optimizations:

| Optimization | State Reduction | Precision Loss | When to Use |
|-------------|----------------|----------------|-------------|
| Message Filtering | 80-90% | None | Always, if some messages irrelevant |
| Symmetry Reduction | 2-10x | None | When you have identical components |
| Per-Message Bounds | 50-80% | None | When operations have different concurrency |
| Temporal Constraints | 30-60% | Minimal* | When you have known ordering requirements |
| Bounded Exploration | Varies | Moderate** | When depth can be limited |

\* Minimal if constraints are correct; high if constraints are wrong
\*\* Won't find bugs beyond maxDepth

**Combined Impact**: Using all applicable optimizations can achieve 90-95% state space reduction.

---

## Troubleshooting

### Verification still too slow

1. **Check your message filtering**: Run `polly verify` and look for the log line showing message count. Is it still high?
   ```
   [INFO] Message filtering (include): 43 → 7 message types
   ```

2. **Review per-message bounds**: Are your bounds realistic? Setting `maxInFlight: 5` for all message types explores many unrealistic scenarios.

3. **Add temporal constraints**: Look at your message handlers. Are there obvious ordering requirements you haven't declared?

4. **Use bounded exploration**: Start with `maxDepth: 10` and gradually increase if needed.

5. **Consider your state size**: Large state types (big arrays, maps) increase the state space. Can you bound them smaller?

### Verification failing with temporal constraints

**Symptom**: `TemporalConstraint1` invariant violated

**Cause**: Your constraint is too strict, or there's a bug in your application.

**Debug**:
1. Look at the TLC trace showing the violation
2. Check if the violation represents a real bug or an incorrect constraint
3. If the constraint is wrong, adjust or remove it
4. If it's a real bug, fix your application code

### Message types not being filtered

**Symptom**: TLA+ still has all 43 message types despite `include` filter

**Cause**: Message types in `include` must exactly match the message type strings in your code.

**Fix**: Check your message definitions in `src/messages/index.ts` and ensure exact string matches.

---

## Best Practices

1. **Start with Tier 1**: Apply message filtering and per-message bounds first. These are safe and often sufficient.

2. **Measure before optimizing**: Run `polly verify` without optimizations to see baseline performance. This helps you measure improvement.

3. **Optimize incrementally**: Add one optimization at a time and re-run verification. This helps you understand the impact of each change.

4. **Use `--optimize` for guidance**: The AI assistant can suggest project-specific optimizations you might not have considered.

5. **Verify your constraints**: Temporal constraints must be correct. If you're unsure, don't use them.

6. **Document your decisions**: Add comments to your verification config explaining why you chose specific bounds or constraints.

7. **Re-verify after changes**: When you add new message types or change handlers, re-run verification to ensure optimizations are still valid.

---

## Related Documentation

- [Issue #12: Message Type Filtering](https://github.com/fairfoxai/polly/issues/12) - Original feature request
- [TLA+ Symmetry Sets](https://lamport.azurewebsites.net/tla/advanced-examples.html) - TLC documentation on symmetry
- [Verification Configuration Reference](./VERIFICATION.md) - Complete config schema
- [Teaching Command](./TEACH-COMMAND-DESIGN.md) - Using the AI assistant

---

## FAQ

**Q: Can I use both `include` and `exclude`?**
A: No, use one or the other. `include` is typically clearer and safer.

**Q: How do I know which message types to filter?**
A: Run `polly verify --optimize` and ask the AI assistant. Or manually review your message definitions and filter out UI events, debug logs, and analytics.

**Q: Are temporal constraints safe?**
A: Only if they're correct. An incorrect constraint can hide bugs. Use them for well-understood ordering requirements (like authentication flows).

**Q: What's a good maxDepth value?**
A: Start with 10-15 for fast iteration. Increase to 20-30 for more thorough verification. Only use 50+ if you have time and need deep exploration.

**Q: Can I verify without optimizations?**
A: Yes! Optimizations are optional. If your state space is small enough, you don't need them.

**Q: How do I verify my optimizations didn't break verification?**
A: Compare the generated TLA+ files before and after. The core invariants (TypeOK, NoRoutingLoops) should remain the same. You're just reducing the explored state space.
