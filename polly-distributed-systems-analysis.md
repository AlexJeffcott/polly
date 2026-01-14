# How Polly Solves (and Doesn't Solve) Distributed Systems Problems in SPAs/PWAs

**Date:** 2026-01-05

**Context:** Following the research in `spa-distributed-systems-research.md` which established that SPAs/PWAs are distributed systems, this document analyzes how Polly addresses these challenges.

---

## Executive Summary

Polly is a **triple-purpose framework** that attacks the SPA/PWA distributed systems problem from three angles:

1. **Runtime Solution**: Provides infrastructure for distributed state management with Lamport clocks, conflict resolution, and reactive synchronization
2. **Verification Solution**: Enables formal verification of distributed properties using TLA+ model checking
3. **Documentation Solution**: Automatically generates architecture diagrams documenting distributed system topology and message flows

**Verdict:** Polly solves many of the practical distributed systems problems but has inherent limitations due to the boundaries between static analysis, runtime behavior, and the fundamental impossibility of certain distributed systems guarantees.

---

## Problems Polly Solves Excellently

### 1. ✅ Distributed State Synchronization

**The Problem:**
SPAs/PWAs need to keep state consistent across multiple execution contexts (main thread, service workers, web workers, multiple tabs) without manual serialization and message passing.

**Polly's Solution:**
```typescript
// State automatically syncs across ALL contexts
export const currentUser = $sharedState<User | null>('user', null)

// Update in service worker
currentUser.value = fetchedUser  // Automatically propagates to UI

// UI automatically re-renders
function UserProfile() {
  return <div>{currentUser.value?.name}</div>  // Always in sync!
}
```

**How It Works:**
- Uses **Lamport logical clocks** (README.md:658-666) for causal consistency
- Broadcasts state updates to all contexts
- Applies updates in causal order
- **Deterministic conflict resolution** prevents race conditions

**Impact:** This is HUGE. Polly provides **causal consistency** guarantees that most SPAs simply ignore or handle ad-hoc with buggy implementations.

### 2. ✅ Race Condition Detection (Static Analysis)

**The Problem:**
Concurrent state updates from multiple contexts can lead to race conditions that are nearly impossible to reproduce in testing.

**Polly's Solution:**
```typescript
// Define constraints with requires/ensures
export const userConstraints = $constraints("user.active", {
  PING: {
    requires: "state.user.active === true",
    message: "User must be active to ping"
  }
})
```

**Verification Process:**
1. Extract all message handlers from codebase (verification/README.md:9)
2. Generate TLA+ specification
3. Model check ALL possible interleavings with TLC
4. Find violations before code ships

**Impact:** Catches concurrency bugs that would take months of production use to surface. This is enterprise-grade distributed systems verification brought to SPAs.

### 3. ✅ Explicit State Boundaries

**The Problem:**
SPAs often conflate different kinds of state, leading to over-synchronization or data loss.

**Polly's Solution:**
```typescript
// Synced + persisted (survives reload)
const settings = $sharedState('settings', { theme: 'dark' })

// Synced but not persisted (temporary)
const onlineStatus = $syncedState('online', true)

// Persisted but not synced (local)
const lastOpened = $persistedState('lastOpened', Date.now())

// Local only (ephemeral UI state)
const isLoading = $state(false)
```

**Impact:** Forces developers to think about CAP theorem tradeoffs explicitly. You MUST decide: "Does this need to be synced? Persisted? Both?"

### 4. ✅ Offline-First Patterns

**The Problem:**
Network partitions are inevitable but most SPAs treat them as exceptional edge cases.

**Polly's Solution:**
```typescript
// Cache pattern with automatic fallback (README.md:510-536)
const cache = $sharedState<Record<string, unknown>>('cache', {})

bus.on('API_FETCH', async (payload) => {
  // Check cache first
  if (cache.value[payload.url]) {
    return { success: true, data: cache.value[payload.url], cached: true }
  }

  try {
    const response = await fetch(payload.url)
    const data = await response.json()
    cache.value = { ...cache.value, [payload.url]: data }
    return { success: true, data, cached: false }
  } catch (error) {
    // Fallback to cache if offline (partition tolerance!)
    if (cache.value[payload.url]) {
      return { success: true, data: cache.value[payload.url], cached: true }
    }
    return { success: false, error: error.message }
  }
})
```

**Impact:** This is **exactly** the pattern offline-first PWAs need, with cache invalidation and partition tolerance baked in.

### 5. ✅ Message Ordering Guarantees

**The Problem:**
Network delays mean messages can arrive out-of-order, violating causal dependencies.

**Polly's Solution:**
- Message routing through centralized background hub (README.md:669-674)
- Lamport clocks ensure causal ordering (README.md:658-664)
- TLA+ verification can prove message ordering properties

**Impact:** Provides **causal ordering** without forcing developers to think about vector clocks or happened-before relations.

### 6. ✅ Architecture Documentation & Visualization

**The Problem:**
Distributed systems are inherently difficult to understand and reason about. The complexity of message flows, multiple execution contexts, and asynchronous interactions makes it nearly impossible to keep a mental model of the system without explicit documentation.

**Polly's Solution:**
```bash
polly visualize
```

This command (README.md:453-473):
1. **Analyzes your codebase** to extract architecture
2. **Discovers execution contexts** (background, popup, content scripts, etc.)
3. **Maps message flows** between contexts
4. **Identifies external integrations** (APIs, libraries, Chrome APIs)
5. **Generates Structurizr DSL** (C4 model specification)
6. **Creates visual diagrams** showing the distributed system topology

**What It Documents:**
```
// Generated Structurizr DSL includes:
- System context diagram (high-level view)
- Container diagrams (execution contexts)
- Component diagrams (modules within contexts)
- Dynamic diagrams (message sequences)
- Deployment diagrams (runtime topology)
```

**Example Output:**
```
workspace "My Extension" {
  model {
    user = person "User"

    extension = softwareSystem "Chrome Extension" {
      background = container "Background Service Worker" {
        messageRouter = component "Message Router"
        apiClient = component "API Client"
        stateManager = component "State Manager"
      }

      popup = container "Popup UI"
      contentScript = container "Content Script"

      # Message flows
      popup -> background "Send message"
      background -> contentScript "Forward to tab"
      contentScript -> background "Response"
      background -> popup "Broadcast state update"
    }

    api = softwareSystem "Backend API" {
      description "External REST API"
    }

    background -> api "Fetch data"
  }

  views {
    systemContext extension {
      include *
      autolayout lr
    }

    container extension {
      include *
      autolayout tb
    }

    dynamic extension "User Action Flow" {
      user -> popup "Click button"
      popup -> background "REQUEST_DATA"
      background -> api "GET /data"
      api -> background "Response"
      background -> popup "STATE_UPDATE"
      popup -> user "Display result"
    }
  }
}
```

**Why This Matters for Distributed Systems:**

1. **Conway's Law Recognition**: Distributed systems reflect organizational/architectural boundaries. Visualizing these boundaries makes them explicit.

2. **Communication Pattern Discovery**: Seeing message flows reveals:
   - Request/response patterns
   - Broadcast/publish-subscribe
   - Long-lived connections
   - Synchronous vs asynchronous boundaries

3. **Failure Mode Analysis**: Visual diagrams help identify:
   - Single points of failure (centralized router)
   - Network boundaries where partitions occur
   - Contexts that can crash independently
   - State that needs to survive crashes

4. **Onboarding & Knowledge Transfer**: New developers can understand:
   - "What contexts exist?"
   - "How do they communicate?"
   - "Where does state live?"
   - "What external dependencies exist?"

5. **Architecture Decision Records (ADRs)**: Polly can link ADRs to the diagrams, connecting decisions to structure.

**Integration with Verification:**
The visualization isn't just documentation - it's **input to reasoning**:
- See which message flows need verification
- Identify critical paths for TLA+ modeling
- Understand state flow through the system
- Spot architectural smells (too many dependencies, circular flows)

**Impact:** This solves a **major pain point** in distributed systems: they're invisible. Traditional SPAs hide their distributed nature in ad-hoc `postMessage` calls and callback chains. Polly makes the distributed system **explicit and visual**, which is essential for:
- Debugging race conditions
- Understanding performance bottlenecks
- Planning resilience strategies
- Communicating architecture to stakeholders
- Detecting when the system has become too complex

This is similar to how tools like Kubernetes dashboards visualize microservices topology - you can't manage what you can't see.

---

## Problems Polly Solves Partially

### 7. ⚠️ Conflict Resolution

**What Polly Provides:**
- Last-write-wins semantics with Lamport clocks
- Deterministic conflict resolution (README.md:663)
- Can verify conflict-free properties with TLA+

**What's Missing:**
- No CRDT support out-of-the-box
- No application-specific conflict resolution strategies
- Can't handle semantic conflicts (e.g., "booking the same hotel room")

**Reality Check:**
Polly gives you **syntactic conflict resolution** (which update wins?) but not **semantic conflict resolution** (does this operation make business sense?). For many SPAs, last-write-wins is sufficient. For collaborative apps, you'd need CRDTs on top of Polly.

### 8. ⚠️ Cache Invalidation

**What Polly Provides:**
- Structured cache as `$sharedState`
- Persistence control
- Can verify cache consistency invariants

**What's Missing:**
- No TTL support
- No automatic invalidation strategies
- No stale-while-revalidate patterns
- Manual cache key management

**Reality Check:**
Polly provides the *infrastructure* for cache invalidation but doesn't solve the "two hard problems in computer science" automatically. You still need to design your cache invalidation strategy.

### 9. ⚠️ Network Failure Handling

**What Polly Provides:**
- Offline-first state persistence
- Request/response pattern with explicit error handling
- Can model network failures in TLA+ specs

**What's Missing:**
- No automatic retry logic
- No exponential backoff
- No circuit breaker patterns
- No request deduplication

**Reality Check:**
Polly makes it *easier* to handle network failures but doesn't provide resilience patterns out-of-the-box. You need to implement retry logic yourself.

---

## Problems Polly Cannot Solve (Fundamental Limitations)

### 10. ❌ Runtime Verification of Temporal Properties

**The Limitation:**
TLA+ verification is **static** - it model checks the state space at build time. It cannot verify runtime behavior like:

- "Eventually, this user will be synced within 5 seconds"
- "Response time is < 100ms for 99% of requests"
- "This conflict happens in production under load"

**Why:**
- Static analysis can't predict network latency
- Model checking explores *all possible* interleavings, not *actual* production behavior
- Performance characteristics depend on runtime environment

**Impact:** You get **correctness** guarantees but not **performance** or **liveness** guarantees.

### 11. ❌ Cross-System Verification

**The Limitation:**
Polly verifies the **client-side** of your distributed system. It cannot verify:

- Client-server protocol correctness
- Backend API invariants
- Database consistency with frontend state
- End-to-end distributed transactions

**Why:**
Polly analyzes one codebase. The full distributed system spans multiple services/repos.

**Example of the Gap:**
```typescript
// Polly can verify THIS:
ensures(state.user.id === payload.userId, "IDs must match")

// Polly CANNOT verify THIS:
// "The user ID returned by the API matches the user ID in the database"
// "The API doesn't have a race condition with another client's request"
```

**Impact:** Polly gives you a **verified client**, but not a **verified distributed system**. The server is still a black box.

### 12. ❌ Distributed Transaction Guarantees

**The Limitation:**
Polly provides causal consistency but not:

- Distributed transactions (no two-phase commit)
- Linearizability (can't guarantee real-time ordering across contexts)
- Serializability (can't provide ACID guarantees)

**Why:**
True distributed transactions require coordination protocols (2PC, Paxos, Raft) which have significant performance costs. Polly chose **availability** over **strong consistency** (CAP theorem tradeoff).

**Example:**
```typescript
// This is NOT atomic across contexts:
state.balance.value -= 100
state.purchaseCount.value += 1

// Another context might observe:
// balance decreased but purchaseCount not yet incremented
```

**Impact:** You get **eventual consistency**, not **strong consistency**. For many SPAs this is fine; for financial apps it might not be.

### 13. ❌ Byzantine Fault Tolerance

**The Limitation:**
Polly assumes **honest contexts** (crash-fault tolerance). It doesn't protect against:

- Malicious client-side code
- Tampered state from browser extensions
- XSS attacks modifying state
- Compromised service workers

**Why:**
Byzantine fault tolerance requires cryptographic proofs, quorum consensus, and significant overhead. SPAs fundamentally trust the client environment.

**Impact:** Polly can't make your SPA secure against malicious actors. You still need authentication, authorization, and server-side validation.

### 14. ❌ State Space Explosion

**The Limitation:**
TLA+ model checking suffers from **combinatorial explosion**. From verification/README.md:165-171:

> "State space too large"
> Reduce bounds in verify.config.ts:
> - Lower maxInFlight
> - Lower maxTabs
> - Reduce enum/string value sets

**Why:**
Model checking explores *every possible state*. With N boolean variables, you have 2^N states. Complex SPAs quickly become intractable.

**Practical Example:**
```typescript
// If you have:
// - 5 message types
// - 3 contexts
// - State with 10 boolean flags
// - maxInFlight = 3

// Possible states ≈ 5^3 * 3 * 2^10 * arrangements
// = 125 * 3 * 1024 * (huge) = millions of states
```

**Impact:** Verification is only practical for **critical subsystems**, not entire applications. You must carefully bound the model.

---

## The Fallacies Polly Doesn't Address

Going back to the [8 Fallacies of Distributed Computing](https://en.wikipedia.org/wiki/Fallacies_of_distributed_computing):

| Fallacy | Does Polly Help? |
|---------|------------------|
| The network is reliable | ✅ YES - Offline-first patterns, cache fallback |
| Latency is zero | ⚠️ PARTIAL - Async patterns, but no latency compensation |
| Bandwidth is infinite | ❌ NO - Still need to optimize bundle size |
| The network is secure | ❌ NO - Client-side security is impossible |
| Topology doesn't change | ✅ YES - Automatic reconnection, port management |
| There is one administrator | ❌ NO - Can't control CDNs, ISPs, browser updates |
| Transport cost is zero | ❌ NO - State sync has overhead |
| The network is homogeneous | ⚠️ PARTIAL - Abstraction helps, but browser differences remain |

---

## What Polly Is Really Good At

### The Sweet Spot

Polly excels at **intra-client distributed systems problems**:

1. **Multi-context synchronization** (main thread ↔ service worker ↔ web workers)
2. **Offline-first state management**
3. **Concurrent message handling**
4. **Causal consistency** across client contexts
5. **Static verification** of client-side concurrency properties
6. **Architecture visualization** of complex distributed interactions

This is a **real** distributed system that Polly models, verifies, and documents correctly.

### The Value Proposition

Before Polly, developers would:
1. Manually implement `postMessage` protocols
2. Ad-hoc state synchronization with bugs
3. No verification of race conditions
4. Inconsistent offline behavior
5. Cache invalidation bugs
6. **Undocumented architecture** - system exists only in developers' heads

After Polly, developers get:
1. Declarative state with automatic sync
2. Proven causal consistency
3. TLA+ verification of concurrency
4. Structured offline patterns
5. Clear cache semantics
6. **Automatic architecture diagrams** - system is explicitly visualized

**This is transformative for Chrome extensions and PWAs.**

---

## Where Polly Falls Short

### Outside Polly's Scope

Polly does NOT solve:

1. **Client-Server Protocol Verification**
   - Can't verify the API contract
   - Can't prove server-side correctness
   - No end-to-end transaction guarantees

2. **Network Resilience Patterns**
   - No automatic retry/backoff
   - No circuit breakers
   - No request deduplication
   - No timeout management

3. **Performance & Latency**
   - Can't guarantee response times
   - Can't optimize for network conditions
   - No adaptive strategies

4. **Security**
   - No protection against malicious code
   - Can't prevent state tampering
   - No cryptographic guarantees

5. **Distributed Consensus**
   - No multi-leader replication
   - No distributed transactions
   - No linearizability

### The Gap in the Distributed Systems Stack

```
┌─────────────────────────────────────────┐
│   End-to-End Distributed System         │
├─────────────────────────────────────────┤
│                                          │
│  ┌────────────────────────────────┐     │
│  │   Backend Services             │ ◄───┼─── Polly can't verify this
│  │   - API servers                │     │
│  │   - Databases                  │     │
│  │   - Message queues             │     │
│  └────────────────────────────────┘     │
│              ▲                           │
│              │ HTTP/WebSocket            │
│              │                           │
│  ┌───────────┴────────────────────┐     │
│  │   Client-Side Distributed Sys  │ ◄───┼─── ✅ Polly verifies THIS
│  │   - Main thread                │     │
│  │   - Service worker             │     │
│  │   - Web workers                │     │
│  │   - Multiple tabs              │     │
│  │                                 │     │
│  │   📊 Polly visualizes THIS     │ ◄───┼─── ✅ Makes it comprehensible
│  └────────────────────────────────┘     │
│                                          │
└─────────────────────────────────────────┘
```

Polly solves the **bottom half** brilliantly but can't touch the **top half** or the **boundary** between them.

However, Polly's visualization capability helps bridge the conceptual gap by:
- Making client-server boundaries explicit
- Documenting external API dependencies
- Showing where network calls happen
- Highlighting integration points

---

## Recommendations for Using Polly

### Do Use Polly When:

1. **Building Chrome Extensions**
   - Multiple contexts are unavoidable
   - State sync is painful
   - Background ↔ UI communication is complex
   - → **Polly is perfect here**

2. **Building Offline-First PWAs**
   - Need persistent state
   - Service worker integration
   - Multi-tab synchronization
   - → **Polly handles this elegantly**

3. **Critical Concurrency Properties**
   - User authentication flows
   - Financial transactions (client-side)
   - State machine correctness
   - → **TLA+ verification is invaluable**

4. **Complex Distributed Architectures**
   - Many execution contexts
   - Intricate message flows
   - Need to onboard developers
   - → **Visualization makes it comprehensible**

### Don't Use Polly When:

1. **Simple SPAs**
   - Single context (just main thread)
   - No offline requirements
   - Simple state (React Context is enough)
   - → **Polly is overkill**

2. **Server-Driven Applications**
   - Backend controls all state
   - Client is just a view
   - Server-sent events for updates
   - → **Use traditional SPA patterns**

3. **Strong Consistency Required**
   - Financial transactions requiring ACID
   - Distributed locks needed
   - Linearizability required
   - → **Move logic to backend**

### Polly + Other Tools

Polly works best when combined with:

1. **CRDTs** (for collaborative editing)
   - Use Automerge/Yjs on top of Polly state
   - Polly provides transport, CRDTs provide semantic merge

2. **API Client Libraries** (for network resilience)
   - Use Polly for state sync
   - Use Axios/Fetch with retry for network calls

3. **Server-Side Verification** (for end-to-end correctness)
   - Verify client with Polly TLA+
   - Verify server with separate formal methods
   - Verify protocol with contract testing

4. **Architecture Tools** (for holistic view)
   - Use Polly visualize for client architecture
   - Combine with backend architecture diagrams
   - Link with ADRs for decision context

---

## Conclusion: Polly's Place in the Distributed Systems Landscape

### What Polly Proves

Polly demonstrates that **client-side distributed systems can be tamed** with:
- Proper abstractions (Lamport clocks, message routing)
- Formal verification (TLA+ model checking)
- Explicit state boundaries (shared/synced/persisted/local)
- **Automatic documentation** (Structurizr DSL generation)

This is a **significant achievement** - most SPAs are ad-hoc distributed systems with bugs and no documentation. Polly makes them **correct by construction** and **comprehensible by visualization**.

### What Polly Reminds Us

Even with Polly, you're still building a distributed system. You still face:
- Network unreliability
- Eventual consistency tradeoffs
- Cache invalidation challenges
- Security vulnerabilities
- Performance unpredictability
- **Architectural complexity** that needs documentation

Polly **acknowledges** this reality and gives you tools to handle it. It doesn't pretend the network is a function call, and it doesn't let your architecture become invisible.

### The Bigger Picture

Polly is **necessary but not sufficient** for building robust SPAs/PWAs:

```
Robust SPA/PWA = Polly (client state + verification + docs)
                + Network resilience (retries, circuit breakers)
                + Server-side verification (API correctness)
                + Security (auth, validation)
                + Performance monitoring (observability)
                + End-to-end testing (integration tests)
```

Polly solves the **hardest** parts:
1. Distributed state synchronization with formal verification
2. Making the invisible distributed system visible

But you still need the rest of the stack.

---

## Final Verdict

**Polly helps solve the distributed systems problems in SPAs/PWAs by:**

✅ Providing runtime infrastructure for state synchronization with causal consistency
✅ Enabling static verification of concurrency properties via TLA+
✅ Making offline-first patterns explicit and testable
✅ Forcing developers to think about state boundaries and persistence
✅ Handling the fallacies of distributed computing explicitly
✅ **Generating automatic architecture diagrams that make distributed interactions visible and comprehensible**

**Polly falls short because:**

❌ It only verifies the client, not the full distributed system
❌ Static analysis can't prove runtime performance or liveness
❌ Network resilience patterns are manual
❌ Strong consistency requires moving logic server-side
❌ State space explosion limits verification scope

**The most important contributions:**

1. **Reframes SPA/PWA development as distributed systems engineering** rather than "frontend development"

2. **Provides the tools** (Lamport clocks, formal verification, causal ordering) that distributed systems researchers have used for decades, adapted for the browser environment

3. **Makes the distributed system visible** through automatic architecture visualization, solving the "invisible complexity" problem that plagues most SPAs

This is exactly what the industry needs to stop building buggy, ad-hoc, undocumented distributed systems masquerading as "single page applications".

---

**Related Documents:**
- [spa-distributed-systems-research.md](./spa-distributed-systems-research.md) - The research that motivated this analysis
- [packages/polly/README.md](./packages/polly/README.md) - Polly framework documentation
- [verification/README.md](./verification/README.md) - TLA+ verification guide
- [docs/TLA_RESOURCES.md](./docs/TLA_RESOURCES.md) - TLA+ learning resources
- [docs/ARCHITECTURE.md](./docs/ARCHITECTURE.md) - Chrome extension architecture patterns
