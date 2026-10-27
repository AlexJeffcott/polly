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
  ,BOOKMARKCOUNT_Max       \* Max value for bookmarkCount
  ,MaxMessages_USER_LOGIN
  ,MaxMessages_USER_LOGOUT
  ,MaxMessages_BOOKMARK_ADD
  ,MaxMessages_BOOKMARK_REMOVE
  ,MaxMessages_SETTINGS_UPDATE
  ,MaxMessages_TAB_GET_CURRENT

\* Message types from application
UserMessageTypes == {"USER_LOGIN", "USER_LOGOUT", "BOOKMARK_ADD", "BOOKMARK_REMOVE", "TAB_GET_CURRENT", "SETTINGS_UPDATE", "SETTINGS_GET"}

\* Generic value type for sequences and maps
\* Bounded to 2 values to reduce state space (2^n vs 3^n)
Value == {"v1", "v2"}

\* Generic key type for maps
\* Bounded to allow model checking
Keys == {"k1", "k2"}

\* Application state type definition
State == [
  loginState_loggedIn: BOOLEAN,
  loginState_username: Value,
  bookmarkCount: 0..20
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
  loginState_loggedIn |-> FALSE,
  loginState_username |-> "v1",
  bookmarkCount |-> 0
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

\* Handler for USER_LOGIN
HandleUserLogin(ctx) ==
  /\ contextStates' = [contextStates EXCEPT ![ctx].loginState_loggedIn = TRUE, ![ctx].loginState_username = @]

\* Handler for USER_LOGOUT
HandleUserLogout(ctx) ==
  /\ contextStates[ctx].loginState_loggedIn = TRUE \* Must be logged in to logout
  /\ contextStates[ctx].loginState_loggedIn = TRUE \* Must be logged in to logout
  /\ contextStates' = [contextStates EXCEPT ![ctx].loginState_loggedIn = FALSE]

\* Handler for BOOKMARK_ADD
HandleBookmarkAdd(ctx) ==
  /\ contextStates[ctx].loginState_loggedIn = TRUE \* Must be logged in to add bookmarks
  /\ contextStates[ctx].loginState_loggedIn = TRUE \* Must be logged in to add bookmarks
  /\ contextStates' = [contextStates EXCEPT ![ctx].bookmarkCount = @ + 1]

\* Handler for BOOKMARK_REMOVE
HandleBookmarkRemove(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for TAB_GET_CURRENT
HandleTabGetCurrent(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for TAB_OPEN
HandleTabOpen(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for SETTINGS_UPDATE
HandleSettingsUpdate(ctx) ==
  /\ contextStates[ctx].loginState_loggedIn = TRUE \* Must be logged in to update settings
  /\ contextStates[ctx].loginState_loggedIn = TRUE \* Must be logged in to update settings
  /\ UNCHANGED contextStates

\* Handler for GET_SETTINGS
HandleGetSettings(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for GET_BOOKMARKS
HandleGetBookmarks(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Main state transition action
StateTransition(ctx, msgType) ==
  IF msgType = "USER_LOGIN" THEN HandleUserLogin(ctx)
  ELSE IF msgType = "USER_LOGOUT" THEN HandleUserLogout(ctx)
  ELSE IF msgType = "BOOKMARK_ADD" THEN HandleBookmarkAdd(ctx)
  ELSE IF msgType = "BOOKMARK_REMOVE" THEN HandleBookmarkRemove(ctx)
  ELSE IF msgType = "TAB_GET_CURRENT" THEN HandleTabGetCurrent(ctx)
  ELSE IF msgType = "TAB_OPEN" THEN HandleTabOpen(ctx)
  ELSE IF msgType = "SETTINGS_UPDATE" THEN HandleSettingsUpdate(ctx)
  ELSE IF msgType = "GET_SETTINGS" THEN HandleGetSettings(ctx)
  ELSE IF msgType = "GET_BOOKMARKS" THEN HandleGetBookmarks(ctx)
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

\* Must login before logout
TemporalConstraint1 ==
  \* If USER_LOGOUT has been delivered, then USER_LOGIN must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "USER_LOGOUT")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "USER_LOGIN")

\* Must be logged in to add bookmarks
TemporalConstraint2 ==
  \* If BOOKMARK_ADD has been delivered, then USER_LOGIN must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "BOOKMARK_ADD")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "USER_LOGIN")

\* Must be logged in to update settings
TemporalConstraint3 ==
  \* If SETTINGS_UPDATE has been delivered, then USER_LOGIN must have been delivered
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "SETTINGS_UPDATE")
  =>
  (\E i \in 1..Len(messages) : messages[i].id \in delivered /\ messages[i].msgType = "USER_LOGIN")

\* State constraint to bound state space
StateConstraint ==
  /\ Len(messages) <= MaxMessages
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "USER_LOGIN"}) <= MaxMessages_USER_LOGIN
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "USER_LOGOUT"}) <= MaxMessages_USER_LOGOUT
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "BOOKMARK_ADD"}) <= MaxMessages_BOOKMARK_ADD
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "BOOKMARK_REMOVE"}) <= MaxMessages_BOOKMARK_REMOVE
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "SETTINGS_UPDATE"}) <= MaxMessages_SETTINGS_UPDATE
  /\ Cardinality({m \in DOMAIN messages : messages[m].msgType = "TAB_GET_CURRENT"}) <= MaxMessages_TAB_GET_CURRENT
  /\ TLCGet("level") <= 4 \* Tier 2: Bounded exploration
  \* BookmarksRequireLogin: Cannot have bookmarks without being logged in
  /\ \A ctx \in Contexts : (contextStates[ctx].bookmarkCount <= 0 \/ contextStates[ctx].loginState_loggedIn = TRUE)

\* =============================================================================
\* Temporal Properties
\* =============================================================================

\* ensures(...) for USER_LOGIN: User must be logged in after login
EnsuresAfter_HandleUserLogin == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "USER_LOGIN")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
         contextStates'[target].loginState_loggedIn = TRUE]_allVars

\* ensures(...) for USER_LOGOUT: User must be logged out after logout
EnsuresAfter_HandleUserLogout == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "USER_LOGOUT")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
         contextStates'[target].loginState_loggedIn = FALSE]_allVars

\* ensures(...) for BOOKMARK_ADD: Bookmark count must be positive after add
EnsuresAfter_HandleBookmarkAdd == [][
  \A m \in 1..Len(messages) :
    (messages[m].status = "pending"
     /\ messages'[m].status = "delivered"
     /\ messages[m].msgType = "BOOKMARK_ADD")
    => LET target == messages'[m].deliveredTo IN
         (target \in Contexts /\ ports[target] = "connected")
         =>
         contextStates'[target].bookmarkCount > 0]_allVars

=============================================================================