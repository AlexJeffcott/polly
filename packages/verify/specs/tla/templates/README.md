# TLA+ Architecture Templates

This directory contains reusable TLA+ templates for different application architectures. Each template provides architecture-specific invariants and type definitions that can be imported into generated specifications.

## Available Templates

### `websocket-server.tla`
**Architecture**: Hub-and-spoke WebSocket server
**Use for**: Bun WebSocket apps, Socket.io servers, real-time collaborative systems

**Key Invariants**:
- `ServerAlwaysAvailable`: Server never disconnects
- `ClientsRouteToServer`: All client messages target server
- `BroadcastReachesAllClients`: Broadcasts reach all connected clients
- `NoClientToClientMessages`: Enforces hub-and-spoke topology
- `ClientConnectionConsistency`: Messages only sent/received when connected
- `NoMessageLossOnConnectedPaths`: No drops on healthy connections

**Constants**:
- `MaxClients`: Maximum concurrent WebSocket clients to model
- `MaxMessagesPerClient`: Per-client message limit

### `chrome-extension.tla`
**Architecture**: Multi-context Chrome extension
**Use for**: Chrome/Edge/Firefox extensions with background + content scripts

**Key Invariants**:
- `BackgroundIsSingleton`: Only one background context
- `ContentScriptsAreTabScoped`: Content scripts always have tabId
- `NoRoutingLoops`: Messages don't cycle back to sender
- `TabIsolation`: Content scripts in different tabs are isolated
- `ValidMessagingTopology`: Enforces extension messaging architecture

**Constants**:
- `MaxTabId`: Maximum tab ID to model (bounds content script instances)

### `generic.tla`
**Architecture**: Generic message-passing system
**Use for**: Custom architectures, event buses, actor systems

**Key Invariants**:
- Basic message delivery guarantees
- No message loss
- Eventual consistency

**Constants**:
- `MaxContexts`: Maximum concurrent execution contexts

## Usage

### In Generated Specifications

When the TLA+ generator detects your project type, it automatically includes the appropriate template:

```tla
------------------------- MODULE YourApp -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, MessageRouter

\* Import architecture-specific invariants
INSTANCE WebSocketServer
WITH MaxClients <- 5, MaxMessagesPerClient <- 3

\* Your application-specific spec
\* ...
```

### Manual Import

You can also manually import templates in custom specifications:

```tla
EXTENDS WebSocketServer

\* Use template invariants in your spec
INVARIANTS
  ServerAlwaysAvailable(ports)
  ClientsRouteToServer(messages)
```

## Creating Custom Templates

To create a template for a new architecture:

1. Create a new `.tla` file in this directory
2. Define architecture-specific constants
3. Define architecture-specific invariants
4. Document the invariants clearly
5. Add to the TLA generator's template selection logic

### Template Structure

```tla
------------------------- MODULE YourArchitecture -------------------------
(*
  Description of the architecture pattern

  Usage notes

  Key invariants
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

\* Constants
CONSTANTS
    YourConstant1,
    YourConstant2

\* Type definitions
YourTypes == { ... }

\* Invariants with documentation
YourInvariant(args) ==
    \* Invariant logic
    ...

=============================================================================
```

## Architecture Decision Records

For more context on why specific invariants exist, see:
- [ADR-001: WebSocket Hub-and-Spoke Pattern](../../../docs/adr/001-websocket-hub-spoke.md)
- [ADR-002: Extension Context Isolation](../../../docs/adr/002-extension-context-isolation.md)

## Testing Templates

Templates are tested as part of the integration test suite:
```bash
bun test packages/verify/src/__tests__/templates.test.ts
```

## References

- [TLA+ Language Reference](https://lamport.azurewebsites.net/tla/summary.pdf)
- [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html)
- [Learn TLA+](https://learntla.com/)
