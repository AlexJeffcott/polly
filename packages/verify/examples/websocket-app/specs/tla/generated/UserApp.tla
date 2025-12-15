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

\* Constants for WebSocket template
CONSTANTS MaxClients, MaxMessagesPerClient

\* Import WebSocket server invariants
INSTANCE WebSocketServer

\* Application-specific constants
CONSTANTS
  CONNECTIONS_COUNT_Max       \* Max value for connections.count
  ,CONNECTIONS_MAXCONCURRENT_Max       \* Max value for connections.maxConcurrent
  ,USERS_ONLINE_Max       \* Max value for users.online
  ,USERS_TOTAL_Max       \* Max value for users.total
  ,CHAT_MESSAGECOUNT_Max       \* Max value for chat.messageCount
  ,CHAT_MAXMESSAGES_Max       \* Max value for chat.maxMessages
  ,TODOS_COUNT_Max       \* Max value for todos.count
  ,TODOS_COMPLETED_Max       \* Max value for todos.completed
  ,TODOS_MAXTODOS_Max       \* Max value for todos.maxTodos

\* Message types from application
UserMessageTypes == {"SIGINT"}

\* Generic value type for sequences and maps
\* Bounded to allow model checking
Value == {"v1", "v2", "v3"}

\* Generic key type for maps
\* Bounded to allow model checking
Keys == {"k1", "k2", "k3"}

\* Application state type definition
State == [
  connections_count: 0..100,
  connections_maxConcurrent: 100..100,
  users_online: 0..100,
  users_total: 0..1000,
  chat_messageCount: 0..100,
  chat_maxMessages: 100..100,
  todos_count: 0..50,
  todos_completed: 0..50,
  todos_maxTodos: 50..50,
  system_initialized: {"false", "true"},
  system_dbConnected: {"false", "true"}
]

\* Application state per context
VARIABLE contextStates

\* All variables (extending MessageRouter vars)
allVars == <<ports, messages, pendingRequests, delivered, routingDepth, time, contextStates>>

\* Initial application state
InitialState == [
  connections_count |-> 0,
  connections_maxConcurrent |-> 100,
  users_online |-> 0,
  users_total |-> 0,
  chat_messageCount |-> 0,
  chat_maxMessages |-> 100,
  todos_count |-> 0,
  todos_completed |-> 0,
  todos_maxTodos |-> 50,
  system_initialized |-> "false",
  system_dbConnected |-> "false"
]

\* Initial state (extends MessageRouter)
UserInit ==
  /\ Init  \* MessageRouter's init
  /\ contextStates = [c \in Contexts |-> InitialState]

\* =============================================================================
\* Application-specific actions
\* =============================================================================

\* State transitions extracted from message handlers

\* Handler for SIGINT
HandleSigint(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Main state transition action
StateTransition(ctx, msgType) ==
  IF msgType = "SIGINT" THEN HandleSigint(ctx)
  ELSE UNCHANGED contextStates  \* Unknown message type

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
                 THEN \* Successful delivery - route AND invoke handler
                      /\ messages' = [messages EXCEPT ![msgIndex].status = "delivered"]
                      /\ delivered' = delivered \union {msg.id}
                      /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                             pendingRequests[id]]
                      /\ time' = time + 1
                      /\ StateTransition(target, msg.msgType)
                 ELSE \* Port not connected - message fails
                      /\ messages' = [messages EXCEPT ![msgIndex].status = "failed"]
                      /\ pendingRequests' = [id \in DOMAIN pendingRequests \ {msg.id} |->
                                             pendingRequests[id]]
                      /\ time' = time + 1
                      /\ UNCHANGED <<delivered, contextStates>>
        /\ UNCHANGED ports

\* Next state relation (extends MessageRouter)
UserNext ==
  \/ \E c \in Contexts : ConnectPort(c) /\ UNCHANGED contextStates
  \/ \E c \in Contexts : DisconnectPort(c) /\ UNCHANGED contextStates
  \/ \E src \in Contexts : \E targetSet \in (SUBSET Contexts \ {{}}) : \E tab \in 0..MaxTabId : \E msgType \in UserMessageTypes :
    SendMessage(src, targetSet, tab, msgType) /\ UNCHANGED contextStates
  \/ \E i \in 1..Len(messages) : UserRouteMessage(i)
  \/ CompleteRouting /\ UNCHANGED contextStates
  \/ \E i \in 1..Len(messages) : TimeoutMessage(i) /\ UNCHANGED contextStates

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

\* State constraint to bound state space
StateConstraint ==
  Len(messages) <= MaxInFlight

=============================================================================