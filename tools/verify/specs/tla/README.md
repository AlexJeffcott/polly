# TLA+ Formal Specification for MessageRouter

This directory contains formal specifications for the web extension's message routing system using TLA+ (Temporal Logic of Actions).

## What is This?

TLA+ is a formal specification language for concurrent and distributed systems. It allows us to:
- **Model** the message routing logic mathematically
- **Verify** properties like "no routing loops" or "messages eventually deliver"
- **Find edge cases** that are hard to catch with traditional testing
- **Document** the system behavior precisely

## What We're Verifying

### Core Properties

1. **NoRoutingLoops** - Messages never create infinite routing cycles
2. **EventualResolution** - Every message eventually resolves (delivers, fails, or times out)
3. **ConnectedEventuallyDelivers** - Messages to connected ports eventually deliver
4. **NoOrphanedRequests** - Pending requests always have corresponding messages
5. **TypeOK** - All data structures maintain correct types

### System Model

The spec models:
- **Contexts**: background, content, popup, devtools, options, offscreen
- **Port lifecycle**: disconnected ⇒ connected ⇒ disconnected
- **Message states**: pending → routing → delivered/failed/timeout
- **Routing depth tracking** (for loop detection)
- **Timeout handling**
- **Broadcast semantics**

## Running the Model Checker

### Prerequisites

Docker must be running. The TLA+ toolchain runs in a container.

### Quick Start

```bash
# From project root
bun run tla:up       # Start container
bun run tla:check    # Run model checker
bun run tla:down     # Stop container
```

### Manual Commands

```bash
# Start the TLA+ container
docker-compose -f specs/docker-compose.yml up -d

# Run the model checker
docker-compose -f specs/docker-compose.yml exec tla tlc MessageRouter.tla

# Interactive shell (for exploring)
docker-compose -f specs/docker-compose.yml exec tla sh

# Stop the container
docker-compose -f specs/docker-compose.yml down
```

## Understanding the Output

### Success
```
TLC2 Version X.X.X
...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = X.X%
...
Finished in XXms at (YYYY-MM-DD HH:MM:SS)
```

### Violation Found
TLC will print:
- **Which invariant was violated**
- **The execution trace** (sequence of states) leading to the violation
- Each state shows the values of all variables

Example:
```
Error: Invariant NoRoutingLoops is violated.

State 1: <Initial State>
/\ ports = ...
/\ routingDepth = 0
...

State 2: <ConnectPort("background")>
/\ ports = [background |-> "connected", ...]
...

State 3: <SendMessage("background", "content", 1)>
...
```

## Editing the Spec

### Files

- **MessageRouter.tla** - Main specification (edit this)
- **MessageRouter.cfg** - Model configuration (constants, invariants to check)

### Workflow

1. Edit `.tla` file locally (syntax highlighting via VSCode TLA+ extension)
2. Save changes (files are volume-mounted into container)
3. Run `bun run tla:check`
4. Iterate on violations

### Expanding the Model

Current model is intentionally simple (3 contexts, 4 messages max). To expand:

1. **Add more contexts**: Edit `MessageRouter.cfg`:
   ```
   Contexts = {background, content, popup, devtools, options}
   ```

2. **Increase message limit**: (Warning: state space grows exponentially!)
   ```
   MaxMessages = 6
   ```

3. **Add new properties**: Define in `.tla`, add to `.cfg` under `INVARIANTS` or `PROPERTIES`

4. **Model request/response pairing**: Extend `Message` type with response IDs

## Performance Notes

Model checking explores **all possible states**. State space grows exponentially with:
- Number of contexts
- Number of messages
- Number of tabs

Current settings (3 contexts, 4 messages) check ~10,000 states in <1 second.

Increasing to 5 contexts + 6 messages = ~1 million states = ~10 seconds.

## Relationship to Code

The spec is **not** the implementation - it's a mathematical model.

**Code → Spec mapping:**
- `MessageRouter.routeMessage()` → `RouteMessage` action
- `port.onDisconnect()` → `DisconnectPort` action
- `pendingRequests` Map → `pendingRequests` variable
- "no loops" tests → `NoRoutingLoops` invariant

**Use TLA+ to:**
1. Find edge cases → Add as unit tests
2. Verify design before implementing
3. Document complex concurrent behavior

**Don't use TLA+ for:**
- Testing implementation details (use bun test)
- Performance testing
- Browser API quirks

## Learning Resources

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [Practical TLA+](https://www.apress.com/gp/book/9781484238288) (book)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)

## Next Steps

Potential expansions:
- [ ] Model request/response pairing with IDs
- [ ] Model port reconnection scenarios
- [ ] Add tabId-specific routing
- [ ] Model MessageBus interaction
- [ ] Verify broadcast reaches all ports exactly once
- [ ] Model race conditions during port disconnect
