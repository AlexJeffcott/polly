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
  TODOS_MaxLength  \* Max length for todos

\* Message types from application
UserMessageTypes == {"API_REQUEST", "API_BATCH", "CONTEXT_MENU_CREATE", "CONTEXT_MENU_REMOVE", "LOG", "LOGS_GET", "LOGS_CLEAR", "LOGS_EXPORT", "DOM_QUERY", "DOM_UPDATE", "DOM_INSERT", "DOM_REMOVE", "DEVTOOLS_INSPECT_ELEMENT", "CLIPBOARD_WRITE", "CLIPBOARD_WRITE_HTML", "CLIPBOARD_WRITE_RICH", "CLIPBOARD_READ", "PAGE_EVAL", "PAGE_GET_VAR", "PAGE_CALL_FN", "PAGE_SET_VAR", "STATE_SYNC", "USER_LOGIN", "USER_LOGOUT", "TODO_ADD", "TODO_TOGGLE", "TODO_REMOVE", "TODO_CLEAR_COMPLETED", "GET_STATE", "GET_TODOS"}

\* Generic value type for sequences and maps
\* Bounded to allow model checking
Value == {"v1", "v2", "v3"}

\* Generic key type for maps
\* Bounded to allow model checking
Keys == {"k1", "k2", "k3"}

\* Application state type definition
State == [
  user_loggedIn: BOOLEAN,
  user_role: {"guest", "user", "admin"},
  user_id: {"guest", "user1", "user2", "user3"},
  user_name: {"Guest", "User1", "User2", "Admin"},
  todos: Seq(Value),
  filter: {"all", "active", "completed"}
]

\* Application state per context
VARIABLE contextStates

\* All variables (extending MessageRouter vars)
allVars == <<ports, messages, pendingRequests, delivered, routingDepth, time, contextStates>>

\* Initial application state
InitialState == [
  user_loggedIn |-> FALSE,
  user_role |-> "guest",
  user_id |-> "guest",
  user_name |-> "Guest",
  todos |-> <<>>,
  filter |-> "all"
]

\* Initial state (extends MessageRouter)
UserInit ==
  /\ Init  \* MessageRouter's init
  /\ contextStates = [c \in Contexts |-> InitialState]

\* =============================================================================
\* Application-specific actions
\* =============================================================================

\* State transitions extracted from message handlers

\* Handler for API_REQUEST
HandleApiRequest(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for API_BATCH
HandleApiBatch(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for CONTEXT_MENU_CREATE
HandleContextMenuCreate(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for CONTEXT_MENU_REMOVE
HandleContextMenuRemove(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for LOG
HandleLog(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for LOGS_GET
HandleLogsGet(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for LOGS_CLEAR
HandleLogsClear(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for LOGS_EXPORT
HandleLogsExport(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for DOM_QUERY
HandleDomQuery(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for DOM_UPDATE
HandleDomUpdate(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for DOM_INSERT
HandleDomInsert(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for DOM_REMOVE
HandleDomRemove(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for DEVTOOLS_INSPECT_ELEMENT
HandleDevtoolsInspectElement(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for CLIPBOARD_WRITE
HandleClipboardWrite(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for CLIPBOARD_WRITE_HTML
HandleClipboardWriteHtml(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for CLIPBOARD_WRITE_RICH
HandleClipboardWriteRich(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for CLIPBOARD_READ
HandleClipboardRead(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for PAGE_EVAL
HandlePageEval(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for PAGE_GET_VAR
HandlePageGetVar(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for PAGE_CALL_FN
HandlePageCallFn(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for PAGE_SET_VAR
HandlePageSetVar(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for STATE_SYNC
HandleStateSync(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for USER_LOGIN
HandleUserLogin(ctx) ==
  /\ contextStates[ctx].user_loggedIn = FALSE \* User must not be logged in
  /\ payload.userId # NULL /\ payload.userId_length > 0 \* User ID must be provided
  /\ payload.name_length > 0 \* User name must be provided
  /\ contextStates' = [contextStates EXCEPT
    ![ctx].user_loggedIn = TRUE
  ]
  /\ contextStates'[ctx].user_loggedIn = TRUE \* User must be logged in
  /\ contextStates'[ctx].user_id = payload.userId \* User ID must match payload
  /\ contextStates'[ctx].user_role # 'guest' \* User must have non-guest role

\* Handler for USER_LOGOUT
HandleUserLogout(ctx) ==
  /\ contextStates[ctx].user_loggedIn = TRUE \* User must be logged in to logout
  /\ contextStates' = [contextStates EXCEPT
    ![ctx].user_loggedIn = FALSE,
    ![ctx].user_id = "user3",
    ![ctx].user_name = "Guest",
    ![ctx].user_role = "guest"
  ]
  /\ contextStates'[ctx].user_loggedIn = FALSE \* User must be logged out
  /\ contextStates'[ctx].user_role = 'guest' \* User must have guest role
  /\ contextStates'[ctx].user_id = NULL \* User ID must be null

\* Handler for TODO_ADD
HandleTodoAdd(ctx) ==
  /\ contextStates[ctx].todos_length < 100 \* Cannot exceed 100 todos
  /\ payload.text_length > 0 \* Todo text cannot be empty
  /\ payload.text_length <= 500 \* Todo text too long
  /\ UNCHANGED contextStates
  /\ contextStates'[ctx].todos_length = previousCount + 1 \* Todo count must increase by 1
  /\ contextStates'[ctx].todos_length > 0 \* Todo count must be positive
  /\ contextStates'[ctx].todos_length <= 100 \* Todo count must not exceed 100

\* Handler for TODO_TOGGLE
HandleTodoToggle(ctx) ==
  /\ todo # undefined \* Todo must exist
  /\ UNCHANGED contextStates

\* Handler for TODO_REMOVE
HandleTodoRemove(ctx) ==
  /\ index >= 0 \* Todo must exist
  /\ UNCHANGED contextStates
  /\ contextStates'[ctx].todos_length = previousCount - 1 \* Todo count must decrease by 1
  /\ contextStates'[ctx].todos_findIndex(t => t.id = payload.id) = -1 \* Todo must be removed

\* Handler for TODO_CLEAR_COMPLETED
HandleTodoClearCompleted(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates
  /\ contextStates'[ctx].todos_length = previousCount - completedCount \* Removed count must match completed count
  /\ contextStates'[ctx].todos_every(t => ~t.completed) \* All remaining todos must be incomplete

\* Handler for GET_STATE
HandleGetState(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Handler for GET_TODOS
HandleGetTodos(ctx) ==
  \* No state changes in handler
  /\ UNCHANGED contextStates

\* Main state transition action
StateTransition(ctx, msgType) ==
  IF msgType = "API_REQUEST" THEN HandleApiRequest(ctx)
  ELSE IF msgType = "API_BATCH" THEN HandleApiBatch(ctx)
  ELSE IF msgType = "CONTEXT_MENU_CREATE" THEN HandleContextMenuCreate(ctx)
  ELSE IF msgType = "CONTEXT_MENU_REMOVE" THEN HandleContextMenuRemove(ctx)
  ELSE IF msgType = "LOG" THEN HandleLog(ctx)
  ELSE IF msgType = "LOGS_GET" THEN HandleLogsGet(ctx)
  ELSE IF msgType = "LOGS_CLEAR" THEN HandleLogsClear(ctx)
  ELSE IF msgType = "LOGS_EXPORT" THEN HandleLogsExport(ctx)
  ELSE IF msgType = "DOM_QUERY" THEN HandleDomQuery(ctx)
  ELSE IF msgType = "DOM_UPDATE" THEN HandleDomUpdate(ctx)
  ELSE IF msgType = "DOM_INSERT" THEN HandleDomInsert(ctx)
  ELSE IF msgType = "DOM_REMOVE" THEN HandleDomRemove(ctx)
  ELSE IF msgType = "DEVTOOLS_INSPECT_ELEMENT" THEN HandleDevtoolsInspectElement(ctx)
  ELSE IF msgType = "CLIPBOARD_WRITE" THEN HandleClipboardWrite(ctx)
  ELSE IF msgType = "CLIPBOARD_WRITE_HTML" THEN HandleClipboardWriteHtml(ctx)
  ELSE IF msgType = "CLIPBOARD_WRITE_RICH" THEN HandleClipboardWriteRich(ctx)
  ELSE IF msgType = "CLIPBOARD_READ" THEN HandleClipboardRead(ctx)
  ELSE IF msgType = "PAGE_EVAL" THEN HandlePageEval(ctx)
  ELSE IF msgType = "PAGE_GET_VAR" THEN HandlePageGetVar(ctx)
  ELSE IF msgType = "PAGE_CALL_FN" THEN HandlePageCallFn(ctx)
  ELSE IF msgType = "PAGE_SET_VAR" THEN HandlePageSetVar(ctx)
  ELSE IF msgType = "STATE_SYNC" THEN HandleStateSync(ctx)
  ELSE IF msgType = "USER_LOGIN" THEN HandleUserLogin(ctx)
  ELSE IF msgType = "USER_LOGOUT" THEN HandleUserLogout(ctx)
  ELSE IF msgType = "TODO_ADD" THEN HandleTodoAdd(ctx)
  ELSE IF msgType = "TODO_TOGGLE" THEN HandleTodoToggle(ctx)
  ELSE IF msgType = "TODO_REMOVE" THEN HandleTodoRemove(ctx)
  ELSE IF msgType = "TODO_CLEAR_COMPLETED" THEN HandleTodoClearCompleted(ctx)
  ELSE IF msgType = "GET_STATE" THEN HandleGetState(ctx)
  ELSE IF msgType = "GET_TODOS" THEN HandleGetTodos(ctx)
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
  Len(messages) <= MaxMessages

=============================================================================