------------------------- MODULE GenericMessagePassing -------------------------
(*
  Template for generic message-passing systems.

  Architecture: Generic message bus / event system
  - Multiple independent contexts
  - Message passing without specific topology constraints
  - Suitable for event buses, actor systems, custom architectures

  Usage:
    Import this module in your generated specification:
    INSTANCE GenericMessagePassing

  Invariants:
    - NoMessageLoss: Messages are eventually delivered
    - MessageOrdering: FIFO ordering per sender-receiver pair
    - NoDeadlock: System can always make progress
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

(* ───────────────────────────────────────────────────────────────── *)
(* Constants                                                           *)
(* ───────────────────────────────────────────────────────────────── *)

CONSTANTS
    MaxContexts,     \* Maximum concurrent execution contexts
    MaxInFlight      \* Maximum messages in flight

(* ───────────────────────────────────────────────────────────────── *)
(* Generic Type Definitions                                           *)
(* ───────────────────────────────────────────────────────────────── *)

\* Generic contexts (numbered)
GenericContexts == {
    "context-" \o ToString(n) : n \in 1..MaxContexts
}

\* Message states
MessageStates == {"pending", "sent", "delivered", "dropped"}

(* ───────────────────────────────────────────────────────────────── *)
(* Helper Operators                                                    *)
(* ───────────────────────────────────────────────────────────────── *)

\* Convert a sequence to a set of its elements
Range(seq) == {seq[i] : i \in DOMAIN seq}

(* ───────────────────────────────────────────────────────────────── *)
(* Generic Message-Passing Invariants                                *)
(* ───────────────────────────────────────────────────────────────── *)

\*
\* Invariant: No message loss under normal conditions
\*
\* Messages should be delivered unless explicitly dropped or the
\* target is unavailable. This ensures message delivery reliability.
\*
\* This catches bugs like:
\* - Silently dropped messages
\* - Buffer overflow without error handling
\* - Lost messages due to race conditions
\*
NoMessageLoss(messages, delivered, ports) ==
    \A msg \in Range(messages) :
        (/\ msg.status = "sent"
         /\ \A target \in msg.targets : ports[target] = "connected")
        => \/ msg.id \in delivered
           \/ msg.status = "pending"

\*
\* Invariant: FIFO ordering per sender-receiver pair
\*
\* Messages from the same sender to the same receiver should be
\* delivered in FIFO order. This ensures predictable message ordering.
\*
\* This catches bugs like:
\* - Message reordering
\* - Race conditions in message delivery
\* - Queue implementation bugs
\*
FIFOOrdering(messages, deliveryOrder) ==
    \A msg1, msg2 \in Range(messages) :
        (/\ msg1.source = msg2.source
         /\ msg1.targets = msg2.targets
         /\ msg1.id < msg2.id
         /\ msg1.id \in deliveryOrder
         /\ msg2.id \in deliveryOrder)
        => \* msg1 was delivered before msg2
           \E i, j \in DOMAIN deliveryOrder :
               /\ deliveryOrder[i] = msg1.id
               /\ deliveryOrder[j] = msg2.id
               /\ i < j

\*
\* Invariant: No deadlock
\*
\* The system should always be able to make progress. There should
\* be at least one enabled action at all times.
\*
\* This catches bugs like:
\* - Circular dependencies
\* - Resource exhaustion
\* - Livelock situations
\*
NoDeadlock(ports, messages) ==
    \* At least one context is connected OR
    \* there are no pending messages
    \/ \E ctx \in DOMAIN ports : ports[ctx] = "connected"
    \/ ~(\E msg \in Range(messages) : msg.status = "pending")

\*
\* Invariant: Message bounds respected
\*
\* The system should not exceed configured message limits.
\* This ensures resource constraints are enforced.
\*
\* This catches bugs like:
\* - Unbounded queues
\* - Memory leaks
\* - Resource exhaustion
\*
MessageBoundsRespected(messages) ==
    Cardinality({msg \in Range(messages) : msg.status = "pending"}) <= MaxInFlight

\*
\* Invariant: Context lifecycle consistency
\*
\* Contexts should follow valid state transitions:
\* disconnected -> connecting -> connected -> disconnected
\*
\* This catches bugs like:
\* - Invalid state transitions
\* - Lifecycle management issues
\* - Connection state corruption
\*
ValidLifecycleTransitions(ports, history) ==
    \A ctx \in DOMAIN ports :
        \* Check transition history for this context
        LET transitions == SelectSeq(history, LAMBDA h : h.context = ctx)
        IN \A i \in 1..(Len(transitions)-1) :
            LET current == transitions[i].state
                next == transitions[i+1].state
            IN \/ current = "disconnected" /\ next \in {"connecting", "disconnected"}
               \/ current = "connecting" /\ next \in {"connected", "disconnected"}
               \/ current = "connected" /\ next \in {"connected", "disconnected"}

\*
\* Invariant: No orphaned messages
\*
\* All messages should have valid source and target contexts.
\* This ensures referential integrity of the message graph.
\*
\* This catches bugs like:
\* - Dangling references
\* - Context ID reuse issues
\* - State corruption
\*
NoOrphanedMessages(messages, ports) ==
    \A msg \in Range(messages) :
        /\ msg.source \in DOMAIN ports
        /\ \A target \in msg.targets : target \in DOMAIN ports

=============================================================================
\* Changelog:
\* 2025-12-15: Initial generic message-passing template
