------------------------- MODULE UserApp -------------------------
(*
  Auto-generated TLA+ specification for web extension
  
  Generated from:
    - TypeScript type definitions
    - Verification configuration
  
  This spec extends MessageRouter with:
    - Application-specific state types
    - Message type definitions
    - State transition actions
*)

EXTENDS MessageRouter

\* Application-specific constants
CONSTANTS
  NULL
  ,MaxMessages_ROSTER_PEER_JOINED
  ,MaxMessages_APPLY_PAIR_TOKEN
  ,MaxMessages_OPEN_DATA_CHANNEL
  ,MaxMessages_WRITE_SENTINEL
  ,MaxMessages_RECEIVE_SENTINEL

\* Message types from application
UserMessageTypes == {"peer-candidate", "peer-disconnected", "ROSTER_PEER_JOINED", "APPLY_PAIR_TOKEN", "OPEN_DATA_CHANNEL", "WRITE_SENTINEL", "RECEIVE_SENTINEL"}

\* Generic value type for sequences and maps
\* Bounded to 2 values to reduce state space (2^n vs 3^n)
Value == {"v1", "v2"}

\* Generic key type for maps
\* Bounded to allow model checking
Keys == {"k1", "k2"}

\* Application state type definition
State == [
  aRosterHasB: BOOLEAN,
  aKeyringHasB: BOOLEAN,
  aAdapterKnowsB: BOOLEAN,
  dataChannelOpen: BOOLEAN,
  sentinelWritten: BOOLEAN,
  sentinelObserved: BOOLEAN
]

\* Application state per context
VARIABLE contextStates

\* Message payload (abstract model - non-deterministically chosen)
\* In verification, we model payload fields as potentially any valid value
VARIABLE payload

\* All variables (extending MessageRouter vars)
allVars == <<ports, messages, pendingRequests, delivered, routingDepth, time, contextStates, payload>>

\* Initial application state
InitialState == [
  aRosterHasB |-> FALSE,
  aKeyringHasB |-> FALSE,
  aAdapterKnowsB |-> FALSE,
  dataChannelOpen |-> FALSE,
  sentinelWritten |-> FALSE,
  sentinelObserved |-> FALSE
]

\* Payload modeled with fields: id, text, userId
PayloadType == [id: Value, text: Value, userId: Value]

\* Initial state (extends MessageRouter)
UserInit ==
  /\ Init  \* MessageRouter's init
  /\ contextStates = [c \in Contexts |-> InitialState]
  /\ payload \in PayloadType  \* Non-deterministic initial payload

\* =============================================================================
\* Application-specific actions
\* =============================================================================

\* State transitions extracted from message handlers

\* Handler for peer-candidate
HandlePeerCandidate(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for peer-disconnected
HandlePeerDisconnected(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for ROSTER_PEER_JOINED
HandleRosterPeerJoined(ctx) ==
  /\ contextStates' = [contextStates EXCEPT ![ctx].aRosterHasB = TRUE]

\* Handler for APPLY_PAIR_TOKEN
HandleApplyPairToken(ctx) ==
  /\ contextStates[ctx].aRosterHasB = TRUE \* Pair token in this scenario lands after the signalling roster reports the peer
  /\ contextStates' = [contextStates EXCEPT ![ctx].aKeyringHasB = TRUE, ![ctx].aAdapterKnowsB = TRUE]

\* Handler for OPEN_DATA_CHANNEL
HandleOpenDataChannel(ctx) ==
  /\ contextStates[ctx].aAdapterKnowsB = TRUE \* Data channel can only open once the adapter knows the peer
  /\ contextStates[ctx].aRosterHasB = TRUE \* Data channel can only open once the roster confirms the peer
  /\ contextStates' = [contextStates EXCEPT ![ctx].dataChannelOpen = TRUE]

\* Handler for WRITE_SENTINEL
HandleWriteSentinel(ctx) ==
  /\ contextStates[ctx].dataChannelOpen = TRUE \* Sentinel is written after the channel is open
  /\ contextStates' = [contextStates EXCEPT ![ctx].sentinelWritten = TRUE]

\* Handler for RECEIVE_SENTINEL
HandleReceiveSentinel(ctx) ==
  /\ contextStates[ctx].sentinelWritten = TRUE \* B can only observe a sentinel that A actually wrote
  /\ contextStates[ctx].dataChannelOpen = TRUE \* Receive can only happen across an open data channel
  /\ contextStates' = [contextStates EXCEPT ![ctx].sentinelObserved = TRUE]

\* Main state transition action
StateTransition(ctx, msgType) ==
  IF msgType = "peer-candidate" THEN HandlePeerCandidate(ctx)
  ELSE IF msgType = "peer-disconnected" THEN HandlePeerDisconnected(ctx)
  ELSE IF msgType = "ROSTER_PEER_JOINED" THEN HandleRosterPeerJoined(ctx)
  ELSE IF msgType = "APPLY_PAIR_TOKEN" THEN HandleApplyPairToken(ctx)
  ELSE IF msgType = "OPEN_DATA_CHANNEL" THEN HandleOpenDataChannel(ctx)
  ELSE IF msgType = "WRITE_SENTINEL" THEN HandleWriteSentinel(ctx)
  ELSE IF msgType = "RECEIVE_SENTINEL" THEN HandleReceiveSentinel(ctx)
  ELSE FALSE  \* Unknown message type - action disabled

\* =============================================================================
\* Message Routing with State Transitions
\* =============================================================================

\* Route a message and invoke its handler
UserRouteMessage(msgIndex) ==
  /\ msgIndex \in 1..Len(messages)
  /\ LET msg == messages[msgIndex]
     IN /\ msg.status = "pending"
        /\ routingDepth' = routingDepth + 1
        /\ routingDepth < 5
        /\ \E target \in msg.targets :
              /\ IF target \in Contexts /\ ports[target] = "connected"
                    /\ ENABLED StateTransition(target, msg.msgType)
                 THEN \* Successful delivery - route AND invoke handler
                      /\ messages' = [messages EXCEPT ![msgIndex].status = "delivered",
                                                     ![msgIndex].deliveredTo = target]
                      /\ delivered' = delivered \union {msg.id}
                      /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                             pendingRequests[id]]
                      /\ time' = time + 1
                      /\ \E p \in PayloadType : payload' = p  \* Non-deterministic payload
                      /\ StateTransition(target, msg.msgType)
                 ELSE \* Port not connected, or the handler refused it
                      /\ messages' = [messages EXCEPT ![msgIndex].status = "failed"]
                      /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                             pendingRequests[id]]
                      /\ time' = time + 1
                      /\ UNCHANGED <<delivered, payload, contextStates>>
        /\ UNCHANGED ports

\* Next state relation (extends MessageRouter)
UserNext ==
  \/ \E c \in Contexts : ConnectPort(c) /\ UNCHANGED <<payload, contextStates>>
  \/ \E c \in Contexts : DisconnectPort(c) /\ UNCHANGED <<payload, contextStates>>
  \/ \E src \in Contexts : \E targetSet \in (SUBSET Contexts \ {{}}) : \E tab \in Tabs : \E msgType \in UserMessageTypes :
    SendMessage(src, targetSet, tab, msgType) /\ UNCHANGED <<payload, contextStates>>
  \/ \E i \in 1..Len(messages) : UserRouteMessage(i)
  \/ CompleteRouting /\ UNCHANGED <<payload, contextStates>>
  \/ \E i \in 1..Len(messages) : TimeoutMessage(i) /\ UNCHANGED <<payload, contextStates>>

\* Specification
UserSpec == UserInit /\ [][UserNext]_allVars /\ WF_allVars(UserNext)

\* =============================================================================
\* Application Invariants
\* =============================================================================

\* TypeOK and NoRoutingLoops are inherited from MessageRouter

\* Application state type invariant
UserStateTypeInvariant ==
  \A ctx \in Contexts :
    contextStates[ctx] \in State

\* Tier 2: Temporal constraint invariants
\* Enforce ordering requirements between message types

\* The signalling roster reports peer B before the pair token lands on peer A — the 250ms gap in main.ts
TemporalConstraint1 ==
  \* If APPLY_PAIR_TOKEN has been delivered, then ROSTER_PEER_JOINED must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "APPLY_PAIR_TOKEN")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "ROSTER_PEER_JOINED")

\* The data channel can only open after pairing completes on the daemon side
TemporalConstraint2 ==
  \* If OPEN_DATA_CHANNEL has been delivered, then APPLY_PAIR_TOKEN must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "OPEN_DATA_CHANNEL")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "APPLY_PAIR_TOKEN")

\* The sentinel is written into peer A's $meshState after the channel reports open
TemporalConstraint3 ==
  \* If WRITE_SENTINEL has been delivered, then OPEN_DATA_CHANNEL must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "WRITE_SENTINEL")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "OPEN_DATA_CHANNEL")

\* Peer B observes the sentinel only after peer A writes it
TemporalConstraint4 ==
  \* If RECEIVE_SENTINEL has been delivered, then WRITE_SENTINEL must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "RECEIVE_SENTINEL")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "WRITE_SENTINEL")

\* State constraint to bound state space
StateConstraint ==
  /\ Len(messages) <= MaxMessages
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "ROSTER_PEER_JOINED"}) <= MaxMessages_ROSTER_PEER_JOINED
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "APPLY_PAIR_TOKEN"}) <= MaxMessages_APPLY_PAIR_TOKEN
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "OPEN_DATA_CHANNEL"}) <= MaxMessages_OPEN_DATA_CHANNEL
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "WRITE_SENTINEL"}) <= MaxMessages_WRITE_SENTINEL
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "RECEIVE_SENTINEL"}) <= MaxMessages_RECEIVE_SENTINEL
  /\ TLCGet("level") <= 4 \* Tier 2: Bounded exploration

\* =============================================================================
\* Temporal Properties
\* =============================================================================

\* ensures(...) for ROSTER_PEER_JOINED: Roster must reflect peer-joined after the event fires
EnsuresAfter_HandleRosterPeerJoined == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "ROSTER_PEER_JOINED")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
         contextStates'[target].aRosterHasB = TRUE]_allVars

\* ensures(...) for APPLY_PAIR_TOKEN: Keyring must contain peer after pair token applied; polly#103: applying the pair token must refresh the adapter knownPeers
EnsuresAfter_HandleApplyPairToken == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "APPLY_PAIR_TOKEN")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
             /\ contextStates'[target].aKeyringHasB = TRUE
             /\ contextStates'[target].aAdapterKnowsB = TRUE]_allVars

\* ensures(...) for OPEN_DATA_CHANNEL: Data channel must be open after the open event
EnsuresAfter_HandleOpenDataChannel == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "OPEN_DATA_CHANNEL")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
         contextStates'[target].dataChannelOpen = TRUE]_allVars

\* ensures(...) for WRITE_SENTINEL: Sentinel write must register in shared state
EnsuresAfter_HandleWriteSentinel == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "WRITE_SENTINEL")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
         contextStates'[target].sentinelWritten = TRUE]_allVars

\* ensures(...) for RECEIVE_SENTINEL: Sentinel must be observed after receive; Convergence: a peer that observes A's write must be in A's keyring
EnsuresAfter_HandleReceiveSentinel == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "RECEIVE_SENTINEL")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
             /\ contextStates'[target].sentinelObserved = TRUE
             /\ contextStates'[target].aKeyringHasB = TRUE]_allVars

=============================================================================