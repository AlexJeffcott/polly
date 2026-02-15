# Are SPAs/PWAs Distributed Systems in Denial?

**Research Date:** 2026-01-05

**Thesis:** All SPAs/PWAs are really browser-based applications with a distributed architecture but are in denial about it. This is true in the VAST majority of non-toy cases.

**Conclusion:** ✅ **CONFIRMED** - The evidence strongly supports this thesis.

---

## Executive Summary

Modern Single Page Applications (SPAs) and Progressive Web Apps (PWAs) are distributed systems that face all the classic distributed computing challenges: network unreliability, eventual consistency, conflict resolution, cache invalidation, and partition tolerance. However, the industry terminology ("frontend" vs "backend"), abstraction layers (`fetch()`, `axios`), and framework design choices obscure this reality, leading to poor handling of distributed systems concerns.

---

## Evidence: SPAs/PWAs Are Distributed Systems

### 1. The Fallacies Apply Directly

The most compelling evidence comes from [CSS Wizardry's analysis](https://csswizardry.com/2017/11/the-fallacies-of-distributed-computing-applied-to-front-end-performance/), which explicitly applies the [8 Fallacies of Distributed Computing](https://en.wikipedia.org/wiki/Fallacies_of_distributed_computing) to frontend:

> "Whether we realise it or not, we're in the business of distributed computing: you probably want that CSS file you're writing to make its way from one computer (a server) to another computer (a user's phone) over some kind of network (the internet)."

**All eight fallacies directly impact SPAs:**

1. **The network is NOT reliable** - yet SPAs often have poor offline handling
2. **Latency is NOT zero** - [MIT research shows](https://csswizardry.com/2017/11/the-fallacies-of-distributed-computing-applied-to-front-end-performance/) load-times are more strongly related to network delays than bandwidth
3. **Bandwidth is NOT infinite** - bundle sizes matter
4. **The network is NOT secure** - client-side state is vulnerable
5. **Topology changes** - mobile users constantly switch networks
6. **Multiple administrators** - CDNs, ISPs, client devices
7. **Transport cost isn't zero** - battery, data plans
8. **The network is NOT homogeneous** - 5G vs 3G vs WiFi

### 2. They Face Classic Distributed Systems Problems

#### Conflict Resolution & Eventual Consistency

[Offline-first PWAs](https://gtcsys.com/comprehensive-faqs-guide-data-synchronization-in-pwas-offline-first-strategies-and-conflict-resolution/) must handle:
- Sync conflicts when multiple devices edit while offline
- [Eventual consistency](https://www.geeksforgeeks.org/system-design/cap-theorem-vs-base-consistency-model-distributed-system/) with replication lag (50-200ms cross-region)
- [CAP theorem tradeoffs](https://en.wikipedia.org/wiki/CAP_theorem) - choosing availability over consistency during network partitions

**CAP Theorem Reality:**
> "The CAP theorem states that any distributed data store can provide at most two of the following three guarantees: Consistency, Availability, and Partition Tolerance. No distributed system is safe from network failures, thus network partitioning generally has to be tolerated. In the presence of a partition, one is then left with two options: consistency or availability."

#### Cache Invalidation

As the famous saying goes: ["There are only two hard things in computer science: cache invalidation and naming things"](https://harish-bhattbhatt.medium.com/cache-invalidation-2e3dbe3a5b11).

[Frontend state management](https://dev.to/beggars/on-state-management-and-why-i-stopped-using-it-4di) is essentially distributed cache management:
- [Race conditions in distributed caches](https://medium.com/systems-architectures/distributed-caching-woes-cache-invalidation-c3d389198af3) are "beyond imagination"
- Multiple cache layers (browser, CDN, service worker, localStorage)
- [Consistency problems](https://www.vintasoftware.com/blog/scaling-software-how-to-manage-cache-consistency) across servers and clients

Key challenges:
> "In a distributed environment, managing cache consistency and invalidation becomes a complex challenge due to the presence of multiple cache layers, high data volatility, and potential data inconsistencies."

#### State Synchronization

The [local-first movement](https://www.inkandswitch.com/essay/local-first/) explicitly acknowledges this with [CRDTs](https://loro.dev/) (Conflict-free Replicated Data Types) - mathematical tools from distributed systems research now being applied to web apps.

**Local-First Principles:**
> "Local-first applications store the primary copy of their data in each device's local filesystem, allowing users to read and write data anytime (even offline), which is then synchronized with other devices when a network connection is available."

**CRDT Libraries for Web:**
- **Automerge**: A library of data structures for building collaborative applications
- **Loro**: A high-performance CRDT library for local-first, real-time collaboration
- **Yjs**: An open source realtime sync engine with built-in storage, designed for collaborative design and text editors
- **@localfirst/state**: A Redux-based state container offering seamless synchronization using Automerge CRDTs

### 3. Architecture Has Evolved to Acknowledge This

The 2025 landscape shows recognition:
- [SPAs now integrate with microservices](https://huspi.com/blog-open/definitive-guide-to-spa-why-do-we-need-single-page-applications/) architectures
- [Hybrid approaches](https://merge.rocks/blog/is-single-page-application-dead-in-2025-spas-vs-mpas-vs-islands) (Islands, MPA/SPA splits) acknowledge different consistency requirements
- ["Thin Server Architecture"](https://medium.com/nerd-for-tech/why-single-page-application-spa-architecture-is-so-popular-141b85400204) moves logic to client, creating explicit distributed system

**2025 Architectural Trends:**
> "In 2025, businesses likely need a hybrid approach where marketing sites should be MPA or Islands (Astro/Webflow), while the product (the thing users log into) should be a Single Page Application (Next.js/React)."

---

## The "Denial" Problem

### Why This Happens

#### 1. Terminology Obscures Reality
"Frontend" vs "Backend" creates a false dichotomy. It should be "Client Node" vs "Server Node" in a distributed system.

#### 2. The Network is Abstracted Away
`fetch()` and `axios` make network calls look like function calls, hiding:
- Partial failures
- Retry logic needs
- Timeout considerations
- Idempotency requirements

#### 3. Tools Don't Emphasize Distributed Systems Principles
React/Vue/Angular focus on UI state, not distributed state. You rarely see:
- Built-in exponential backoff
- Conflict resolution strategies
- Vector clocks or logical timestamps
- Explicit partition handling

#### 4. The "Single Page" Metaphor is Misleading
It implies a monolithic, self-contained application when it's really a distributed client node communicating with multiple services.

### Real-World Consequences

[Offline-first architecture resources](https://blog.logrocket.com/offline-first-frontend-apps-2025-indexeddb-sqlite/) highlight that developers must explicitly design for:
- Local storage (IndexedDB, SQLite)
- Background sync queues
- Conflict resolution strategies
- [Advanced sync protocols](https://cushiondb.github.io/)

**Implementation Requirements:**
> "Any type of syncing architecture also needs a conflict resolution solution, which is really the hardest part of this. The main challenge is conflict resolution - when multiple devices edit the same document while offline, you need a strategy to decide which changes win, such as simple last-write-wins based on timestamps or version counters."

This shouldn't be an afterthought - it's fundamental distributed systems engineering.

---

## The Counter-Argument (Very Narrow)

The ONLY cases where an SPA might not be a distributed system:
1. **Fully static sites with zero API calls** (just HTML/CSS/JS assets)
2. **Toy demos that never persist data**

But even these face:
- Asset loading failures (network unreliability)
- CDN issues (multiple administrators)
- Different browser capabilities (heterogeneous network)

So even "trivial" SPAs experience distributed systems problems, they just ignore them poorly.

---

## Key Technical Insights

### Replication Lag in Practice
Typical cloud setup with asynchronous replication:
- Same data center, different racks: **1-5 milliseconds**
- Cross-region (US-East to US-West): **50-100 milliseconds**
- Cross-continent (US to Europe): **100-200 milliseconds**

### Latency Over Bandwidth
Professor Hari Balakrishnan at MIT:
> "…slow load-times are more strongly related to network delays than available bandwidth. Rather than decreasing the number of transferred bytes, we think that reducing the effect of network delays will lead to the most significant speedups."

### Distributed Cache Brittleness
> "Race conditions are common, data in cache is not durable (meaning version information for conflict resolution can get evicted), and a dynamic cache produces race conditions beyond imagination. Distributed cache systems are brittle, with systems becoming unstable, frozen, or dead."

---

## The Recommended Mental Model Shift

### Old (Incorrect) Mental Model:
"I'm building a frontend that talks to a backend."

### New (Correct) Mental Model:
**"I'm building a distributed application where one node happens to run in a browser."**

This shift forces you to think about:
- Network partitions as normal, not exceptional
- Eventual consistency as default, not strong consistency
- Conflict resolution as required, not optional
- Multiple failure modes at every network boundary
- State synchronization across unreliable channels

---

## Conclusion

**The vast majority of SPAs/PWAs are distributed systems in denial.** They:
- ✅ Experience all the classic distributed systems problems
- ✅ Are subject to the CAP theorem
- ✅ Need conflict resolution and eventual consistency
- ✅ Face network partitions and failures
- ✅ Deal with cache invalidation across multiple nodes

The industry is slowly waking up to this with [local-first software](https://localfirstweb.dev/), offline-first architecture, and CRDT adoption. But most SPAs still treat the network as a reliable function call rather than an unreliable message-passing channel between nodes in a distributed system.

---

## References & Sources

### Core Distributed Systems Concepts
- [The Fallacies of Distributed Computing (Applied to Front-End Performance) – CSS Wizardry](https://csswizardry.com/2017/11/the-fallacies-of-distributed-computing-applied-to-front-end-performance/)
- [Fallacies of distributed computing - Wikipedia](https://en.wikipedia.org/wiki/Fallacies_of_distributed_computing)
- [CAP theorem - Wikipedia](https://en.wikipedia.org/wiki/CAP_theorem)
- [CAP Theorem vs. BASE Consistency Model - GeeksforGeeks](https://www.geeksforgeeks.org/system-design/cap-theorem-vs-base-consistency-model-distributed-system/)

### SPAs and Architecture
- [Why Single Page Application (SPA) architecture is so popular? - Medium](https://medium.com/nerd-for-tech/why-single-page-application-spa-architecture-is-so-popular-141b85400204)
- [Is Single Page Application dead in 2025? SPAs vs MPAs vs Islands](https://merge.rocks/blog/is-single-page-application-dead-in-2025-spas-vs-mpas-vs-islands)
- [What is a Single Page Application? SPA vs MPA 2025 - HUSPI](https://huspi.com/blog-open/definitive-guide-to-spa-why-do-we-need-single-page-applications/)

### Offline-First & PWAs
- [Data Synchronization in PWAs: Offline-First Strategies](https://gtcsys.com/comprehensive-faqs-guide-data-synchronization-in-pwas-offline-first-strategies-and-conflict-resolution/)
- [Offline-first frontend apps in 2025: IndexedDB and SQLite - LogRocket](https://blog.logrocket.com/offline-first-frontend-apps-2025-indexeddb-sqlite/)
- [CushionDB](https://cushiondb.github.io/)

### Local-First Software & CRDTs
- [Local-first software: You own your data, in spite of the cloud](https://www.inkandswitch.com/essay/local-first/)
- [Local-First Software](https://localfirstweb.dev/)
- [Loro – Reimagine state management with CRDTs](https://loro.dev/)

### Cache Invalidation & State Management
- [Distributed Caching Woes: Cache Invalidation - Medium](https://medium.com/systems-architectures/distributed-caching-woes-cache-invalidation-c3d389198af3)
- [Cache Invalidation Demystified - Medium](https://harish-bhattbhatt.medium.com/cache-invalidation-2e3dbe3a5b11)
- [Scaling software: cache consistency and invalidation - Vinta](https://www.vintasoftware.com/blog/scaling-software-how-to-manage-cache-consistency)
- [On state management and why I stopped using it - DEV](https://dev.to/beggars/on-state-management-and-why-i-stopped-using-it-4di)

---

## Practical Implications for Developers

### Design Principles
1. **Assume network failure is normal**, not exceptional
2. **Design for partition tolerance first**, then choose consistency vs availability
3. **Implement explicit retry logic** with exponential backoff
4. **Use optimistic UI updates** with rollback capabilities
5. **Build conflict resolution into your data model** from day one
6. **Treat client-side state as a distributed cache** that needs invalidation strategies

### Technology Choices
- Consider **CRDTs** (Automerge, Yjs, Loro) for collaborative features
- Use **service workers** for explicit offline handling
- Implement **IndexedDB or SQLite** for persistent local storage
- Add **background sync** for eventual consistency
- Use **HTTP cache headers** properly instead of reinventing caching

### Testing & Monitoring
- Test with **network throttling** and intermittent failures
- Simulate **concurrent edits** from multiple clients
- Monitor **cache hit rates** and invalidation effectiveness
- Track **sync conflicts** and resolution outcomes
- Measure **time-to-consistency** across the distributed system

---

*This research demonstrates that modern web applications are fundamentally distributed systems, and developers must apply distributed systems principles to build reliable, scalable SPAs and PWAs.*
