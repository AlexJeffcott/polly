------------------------- MODULE WebSocketServer -------------------------
(*
  Template for WebSocket server verification.

  Architecture: Hub-and-spoke pattern
  - Server is central hub
  - Clients connect/disconnect dynamically
  - Messages route through server
  - No direct client-to-client communication

  Usage:
    Import this module in your generated specification:
    INSTANCE WebSocketServer

  Invariants:
    - ServerAlwaysAvailable: Server never disconnects
    - ClientsRouteToServer: All client messages target server
    - BroadcastReachesAllClients: Server broadcasts reach all connected clients
    - NoClientToClientMessages: Clients cannot send directly to each other
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

(* ───────────────────────────────────────────────────────────────── *)
(* Constants                                                           *)
(* ───────────────────────────────────────────────────────────────── *)

CONSTANTS
    MaxClients,          \* Maximum concurrent clients
    MaxMessagesPerClient \* Per-client message limit

(* ───────────────────────────────────────────────────────────────── *)
(* WebSocket-Specific Type Definitions                                *)
(* ───────────────────────────────────────────────────────────────── *)

\* WebSocket contexts (server + numbered clients)
WebSocketContexts == {"server"} \cup {
    "client-" \o ToString(n) : n \in 1..MaxClients
}

\* Connection states for WebSocket nodes
ConnectionStates == {"connected", "disconnected", "connecting"}

(* ───────────────────────────────────────────────────────────────── *)
(* Helper Operators                                                    *)
(* ───────────────────────────────────────────────────────────────── *)

\* Convert a sequence to a set of its elements
Range(seq) == {seq[i] : i \in DOMAIN seq}

(* ───────────────────────────────────────────────────────────────── *)
(* WebSocket-Specific Invariants                                      *)
(* ───────────────────────────────────────────────────────────────── *)

\*
\* Invariant: Server must always be available (never disconnected)
\*
\* In a WebSocket hub-and-spoke architecture, the server is the central
\* hub that all clients communicate through. If the server disconnects,
\* the entire system fails. This invariant ensures the server never
\* enters a disconnected state during verification.
\*
\* This catches bugs like:
\* - Server crashes/exits unexpectedly
\* - Server entering invalid state transitions
\* - Race conditions that break server availability
\*
ServerAlwaysAvailable(ports) ==
    ports["server"] = "connected"

\*
\* Invariant: All client messages must target the server
\*
\* In hub-and-spoke architecture, clients never communicate directly.
\* All messages from clients must be addressed to the server, which
\* then routes messages to appropriate destinations.
\*
\* This catches bugs like:
\* - Clients attempting direct peer-to-peer messaging
\* - Misconfigured routing that bypasses the hub
\* - State corruption that enables forbidden routing paths
\*
ClientsRouteToServer(messages) ==
    \A msg \in Range(messages) :
        (msg.source # "server") => ("server" \in msg.targets)

\*
\* Invariant: Server broadcasts reach all connected clients
\*
\* When the server broadcasts a message to all clients, every connected
\* client should eventually receive it (or the message should be pending).
\* This ensures broadcast reliability.
\*
\* This catches bugs like:
\* - Broadcasts missing some clients
\* - Race conditions in broadcast delivery
\* - Client connection state inconsistencies
\*
BroadcastReachesAllClients(messages, delivered, ports) ==
    \A msg \in Range(messages) :
        (msg.source = "server" /\ msg.targets = WebSocketContexts \ {"server"})
        => (\A client \in msg.targets :
            ports[client] = "connected" =>
            msg.id \in delivered \/ msg.status = "pending")

\*
\* Invariant: No direct client-to-client messages
\*
\* Enforces the hub-and-spoke topology. Clients should never send
\* messages directly to other clients - all communication must route
\* through the server.
\*
\* This catches bugs like:
\* - Topology violations
\* - Security bypasses where clients communicate directly
\* - Misconfigured message routing
\*
NoClientToClientMessages(messages) ==
    \A msg \in Range(messages) :
        (msg.source # "server") =>
        (\A target \in msg.targets : target = "server")

\*
\* Invariant: Client connection state is consistent
\*
\* A client can only send/receive messages when connected.
\* This ensures connection state consistency across the system.
\*
\* This catches bugs like:
\* - Messages sent while disconnected
\* - Connection state race conditions
\* - Stale connection tracking
\*
ClientConnectionConsistency(messages, ports) ==
    \A msg \in Range(messages) :
        (msg.source \in WebSocketContexts /\ msg.source # "server")
        => ports[msg.source] = "connected"

\*
\* Invariant: No message loss on connected paths
\*
\* If both sender and receiver are connected, messages should not be
\* lost. They must either be delivered or still pending.
\*
\* This catches bugs like:
\* - Message drops on healthy connections
\* - Buffer overflow without backpressure
\* - Routing failures
\*
NoMessageLossOnConnectedPaths(messages, delivered, ports) ==
    \A msg \in Range(messages) :
        (/\ ports[msg.source] = "connected"
         /\ \A target \in msg.targets : ports[target] = "connected"
         /\ msg.status = "sent")
        => (msg.id \in delivered \/ msg.status = "pending")

=============================================================================
\* Changelog:
\* 2025-12-15: Initial WebSocket server template with hub-and-spoke invariants
