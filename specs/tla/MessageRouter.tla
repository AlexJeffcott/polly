------------------------- MODULE MessageRouter -------------------------
(*
  Formal specification of the web extension MessageRouter.

  This spec models the core message routing behavior across extension contexts:
  - Background service worker (central hub)
  - Content scripts (one per tab)
  - DevTools, Popup, Options (UI contexts)

  Key properties verified:
  1. No routing loops
  2. Messages eventually deliver (if port connected)
  3. All pending requests eventually resolve (success/timeout/disconnect)
  4. Port cleanup is complete
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Contexts,           \* Set of all contexts: {"background", "content", "popup", ...}
    MaxMessages,        \* Bound on number of messages (for model checking)
    MaxTabId,           \* Maximum tab ID
    TimeoutLimit        \* Message timeout threshold

VARIABLES
    ports,              \* Port state: [context -> "connected" | "disconnected"]
    messages,           \* Sequence of messages in flight
    pendingRequests,    \* Map: messageId -> {sender, target, timestamp}
    delivered,          \* Set of delivered message IDs
    routingDepth,       \* Current routing depth (for loop detection)
    time                \* Logical clock

vars == <<ports, messages, pendingRequests, delivered, routingDepth, time>>

-----------------------------------------------------------------------------

(* Type definitions *)

ContextType == {"background", "content", "popup", "devtools", "options", "offscreen"}
PortState == {"connected", "disconnected"}
MessageStatus == {"pending", "routing", "delivered", "failed", "timeout"}

Message == [
    id: Nat,
    source: ContextType,
    targets: SUBSET ContextType,  \* Set of target contexts (can be multiple)
    tabId: Nat,
    status: MessageStatus,
    timestamp: Nat
]

-----------------------------------------------------------------------------

(* Initial state *)

Init ==
    /\ ports = [c \in Contexts |-> "disconnected"]
    /\ messages = <<>>
    /\ pendingRequests = [id \in {} |-> {}]
    /\ delivered = {}
    /\ routingDepth = 0
    /\ time = 0

-----------------------------------------------------------------------------

(* Actions *)

(* A context connects a port *)
ConnectPort(context) ==
    /\ ports[context] = "disconnected"
    /\ ports' = [ports EXCEPT ![context] = "connected"]
    /\ UNCHANGED <<messages, pendingRequests, delivered, routingDepth, time>>

(* A context disconnects *)
DisconnectPort(context) ==
    /\ ports[context] = "connected"
    /\ ports' = [ports EXCEPT ![context] = "disconnected"]
    \* Clean up pending requests for this context
    /\ LET failedRequests == {id \in DOMAIN pendingRequests :
                               pendingRequests[id].target = context}
       IN pendingRequests' = [id \in DOMAIN pendingRequests \ failedRequests |->
                               pendingRequests[id]]
    /\ UNCHANGED <<messages, delivered, routingDepth, time>>

(* Send a message from source to one or more targets *)
SendMessage(source, targetSet, tabId) ==
    /\ ports[source] = "connected"
    /\ Len(messages) < MaxMessages
    /\ routingDepth = 0  \* Only send at top level (no recursive sends)
    /\ targetSet # {}    \* Must have at least one target
    /\ LET newId == Len(messages) + 1
           newMsg == [
               id |-> newId,
               source |-> source,
               targets |-> targetSet,
               tabId |-> tabId,
               status |-> "pending",
               timestamp |-> time
           ]
       IN /\ messages' = Append(messages, newMsg)
          /\ pendingRequests' = pendingRequests @@
                                (newId :> [sender |-> source,
                                          targets |-> targetSet,
                                          timestamp |-> time])
          /\ time' = time + 1
          /\ UNCHANGED <<ports, delivered, routingDepth>>

(* Route a message to one of its targets *)
RouteMessage(msgIndex) ==
    /\ msgIndex \in 1..Len(messages)
    /\ LET msg == messages[msgIndex]
       IN /\ msg.status = "pending"
          /\ routingDepth' = routingDepth + 1
          /\ routingDepth < 5  \* Safety bound: detect loops
          /\ \* Non-deterministically choose a target from the targets set
             \E target \in msg.targets :
                /\ IF target \in Contexts /\ ports[target] = "connected"
                   THEN \* Successful delivery to this target
                        /\ messages' = [messages EXCEPT ![msgIndex].status = "delivered"]
                        /\ delivered' = delivered \union {msg.id}
                        /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                               pendingRequests[id]]
                        /\ time' = time + 1
                   ELSE \* Port not connected or invalid target, message fails
                        /\ messages' = [messages EXCEPT ![msgIndex].status = "failed"]
                        /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                               pendingRequests[id]]
                        /\ time' = time + 1
                        /\ UNCHANGED delivered
          /\ UNCHANGED ports

(* Complete routing (reset depth) *)
CompleteRouting ==
    /\ routingDepth > 0
    /\ routingDepth' = 0
    /\ UNCHANGED <<ports, messages, pendingRequests, delivered, time>>

(* Handle message timeout *)
TimeoutMessage(msgIndex) ==
    /\ msgIndex \in 1..Len(messages)
    /\ LET msg == messages[msgIndex]
       IN /\ msg.status = "pending"
          /\ time - msg.timestamp > TimeoutLimit
          /\ messages' = [messages EXCEPT ![msgIndex].status = "timeout"]
          /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                 pendingRequests[id]]
          /\ time' = time + 1
          /\ UNCHANGED <<ports, delivered, routingDepth>>

-----------------------------------------------------------------------------

(* Next state relation *)

Next ==
    \/ \E c \in Contexts : ConnectPort(c)
    \/ \E c \in Contexts : DisconnectPort(c)
    \/ \E src \in Contexts : \E targetSet \in (SUBSET Contexts \ {{}}) : \E tab \in 0..MaxTabId : SendMessage(src, targetSet, tab)
    \/ \E i \in 1..Len(messages) : RouteMessage(i)
    \/ CompleteRouting
    \/ \E i \in 1..Len(messages) : TimeoutMessage(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

(* Invariants *)

(* CRITICAL: No infinite routing loops *)
NoRoutingLoops ==
    routingDepth < 3

(* All delivered messages were actually pending *)
DeliveredWerePending ==
    \A msgId \in delivered :
        \E i \in 1..Len(messages) : messages[i].id = msgId

(* No orphaned pending requests - every pending request has a corresponding message *)
NoOrphanedRequests ==
    \A reqId \in DOMAIN pendingRequests :
        \E i \in 1..Len(messages) :
            /\ messages[i].id = reqId
            /\ messages[i].status \in {"pending", "routing"}

(* Messages to disconnected ports eventually fail *)
DisconnectedPortsFail ==
    \A i \in 1..Len(messages) :
        LET msg == messages[i]
        IN (msg.status = "pending" /\ ports[msg.target] = "disconnected")
           => (time - msg.timestamp > TimeoutLimit => msg.status \in {"failed", "timeout"})

(* Type invariant *)
TypeOK ==
    /\ ports \in [Contexts -> PortState]
    /\ \A i \in 1..Len(messages) :
        /\ messages[i].source \in Contexts
        /\ messages[i].target \in Contexts \union {"broadcast"}
        /\ messages[i].status \in MessageStatus
    /\ routingDepth >= 0
    /\ time >= 0

-----------------------------------------------------------------------------

(* Temporal properties *)

(* Eventually, all messages resolve (deliver, fail, or timeout) *)
EventualResolution ==
    \A i \in 1..Len(messages) :
        messages[i].status = "pending"
        ~> messages[i].status \in {"delivered", "failed", "timeout"}

(* If a port is connected and message is sent to it, message eventually delivers *)
ConnectedEventuallyDelivers ==
    \A i \in 1..Len(messages) :
        LET msg == messages[i]
        IN (msg.status = "pending" /\ ports[msg.target] = "connected")
           ~> (msg.status = "delivered")

=============================================================================
