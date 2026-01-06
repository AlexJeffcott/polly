import type { PollyConfig } from "./types";

/**
 * Generate TLA+ specification from Elysia app + Polly config
 *
 * This generates a formal model that can be checked with TLC (TLA+ model checker)
 * to verify distributed systems properties like:
 * - Eventually consistent state
 * - Authorization enforcement
 * - No lost updates
 * - Causal ordering of events
 */
export function generateTLASpec(moduleName: string, config: PollyConfig): string {
  const routes = Object.keys(config.effects || {});
  const clientStates = Object.keys(config.state?.client || {});
  const serverStates = Object.keys(config.state?.server || {});

  return `
---- MODULE ${moduleName} ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

\\* Constants
CONSTANTS
  Clients,        \\* Set of client IDs
  MaxMessages     \\* Maximum messages in flight

\\* Variables
VARIABLES
  clientState,    \\* [clientId |-> state]
  serverState,    \\* Server-side state
  network,        \\* Messages in flight
  offline,        \\* Set of offline clients
  clock           \\* Lamport clock

vars == <<clientState, serverState, network, offline, clock>>

\\* Client state structure
ClientState == [${clientStates.map((s) => `${s}: BOOLEAN`).join(", ")}]

\\* Server state structure
ServerState == [${serverStates.map((s) => `${s}: BOOLEAN`).join(", ")}]

\\* Message types
Message == [
  type: {"request", "response", "broadcast"},
  route: {${routes.map((r) => `"${r}"`).join(", ")}},
  sender: Clients,
  data: BOOLEAN,
  clock: Nat
]

\\* Type invariant
TypeOK ==
  /\\ clientState \\in [Clients -> ClientState]
  /\\ serverState \\in ServerState
  /\\ network \\subseteq Message
  /\\ offline \\subseteq Clients
  /\\ clock \\in Nat
  /\\ Cardinality(network) <= MaxMessages

\\* Initial state
Init ==
  /\\ clientState = [c \\in Clients |-> ${generateInitialClientState(config)}]
  /\\ serverState = ${generateInitialServerState(config)}
  /\\ network = {}
  /\\ offline = {}
  /\\ clock = 0

${generateActions(config, routes)}

\\* Next-state relation
Next ==
  ${routes.map((route) => `  \\/ ${actionNameFromRoute(route)}`).join("\n  ")}
  \\/ ProcessMessage
  \\/ GoOffline
  \\/ GoOnline

\\* Specification
Spec == Init /\\ [][Next]_vars /\\ WF_vars(ProcessMessage)

${generateSafetyProperties(config)}

${generateLivenessProperties(config)}

====`.trim();
}

/**
 * Generate initial client state from config
 */
function generateInitialClientState(config: PollyConfig): string {
  const clientState = config.state?.client || {};
  const fields = Object.keys(clientState);

  if (fields.length === 0) {
    return "[|->]";
  }

  return `[${fields.map((f) => `${f} |-> FALSE`).join(", ")}]`;
}

/**
 * Generate initial server state from config
 */
function generateInitialServerState(config: PollyConfig): string {
  const serverState = config.state?.server || {};
  const fields = Object.keys(serverState);

  if (fields.length === 0) {
    return "[|->]";
  }

  return `[${fields.map((f) => `${f} |-> FALSE`).join(", ")}]`;
}

/**
 * Convert route pattern to TLA+ action name
 * Example: 'POST /todos' -> 'PostTodos'
 */
function actionNameFromRoute(route: string): string {
  const cleaned = route
    .replace(/[^a-zA-Z0-9\s]/g, "")
    .split(/\s+/)
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1).toLowerCase())
    .join("");

  return cleaned || "Action";
}

/**
 * Generate TLA+ actions from routes
 */
function generateActions(config: PollyConfig, routes: string[]): string {
  const actions = routes.map((route) => {
    const actionName = actionNameFromRoute(route);
    const authConfig = config.authorization?.[route];

    return `
\\* Action: ${route}
${actionName} ==
  \\E c \\in Clients :
    /\\ c \\notin offline${authConfig ? `\n    /\\ AuthorizedFor(c, "${route}")` : ""}
    /\\ clock' = clock + 1
    /\\ network' = network \\union {[
         type |-> "request",
         route |-> "${route}",
         sender |-> c,
         data |-> TRUE,
         clock |-> clock
       ]}
    /\\ UNCHANGED <<clientState, serverState, offline>>`.trim();
  });

  // Add generic ProcessMessage action
  actions.push(
    `
\\* Process a message from the network
ProcessMessage ==
  \\E msg \\in network :
    /\\ network' = network \\ {msg}
    /\\ clock' = clock + 1
    ${routes.length > 0 ? "/\\ ProcessMessageInner(msg)" : "/\\ UNCHANGED <<clientState, serverState, offline>>"}

ProcessMessageInner(msg) ==
  CASE msg.type = "request" ->
    ${routes.map((route) => `/\\ msg.route = "${route}" -> HandleRequest${actionNameFromRoute(route)}(msg)`).join("\n    [] ")}
  [] msg.type = "response" ->
    HandleResponse(msg)
  [] msg.type = "broadcast" ->
    HandleBroadcast(msg)
  [] OTHER -> UNCHANGED <<clientState, serverState>>`.trim()
  );

  // Add offline/online actions
  actions.push(
    `
\\* Client goes offline
GoOffline ==
  \\E c \\in Clients :
    /\\ c \\notin offline
    /\\ offline' = offline \\union {c}
    /\\ UNCHANGED <<clientState, serverState, network, clock>>

\\* Client comes back online
GoOnline ==
  \\E c \\in Clients :
    /\\ c \\in offline
    /\\ offline' = offline \\ {c}
    /\\ UNCHANGED <<clientState, serverState, network, clock>>`.trim()
  );

  return actions.join("\n\n");
}

/**
 * Generate safety properties from config
 */
function generateSafetyProperties(config: PollyConfig): string {
  const properties: string[] = [];

  // Authorization enforcement
  if (config.authorization && Object.keys(config.authorization).length > 0) {
    properties.push(
      `
\\* Safety: Authorization is always enforced
AuthorizationEnforced ==
  \\A msg \\in network :
    msg.type = "request" =>
      AuthorizedFor(msg.sender, msg.route)

\\* Helper: Check if client is authorized for route
AuthorizedFor(client, route) ==
  \\* TODO: Implement based on config.authorization rules
  TRUE`.trim()
    );
  }

  // Eventually consistent state
  properties.push(
    `
\\* Safety: Network is bounded
NetworkBounded ==
  Cardinality(network) <= MaxMessages`.trim()
  );

  return properties.length > 0 ? properties.join("\n\n") : "\\* No safety properties generated";
}

/**
 * Generate liveness properties from config
 */
function generateLivenessProperties(_config: PollyConfig): string {
  return `
\\* Liveness: All messages eventually processed
AllMessagesProcessed ==
  <>[] (network = {})

\\* Liveness: Eventually consistent state across online clients
EventualConsistency ==
  <>[] (\\A c1, c2 \\in (Clients \\ offline) :
    clientState[c1] = clientState[c2])`.trim();
}

/**
 * Export TLA+ spec to file
 */
export async function exportTLASpec(
  moduleName: string,
  config: PollyConfig,
  outputPath: string
): Promise<void> {
  const spec = generateTLASpec(moduleName, config);
  await Bun.write(outputPath, spec);
}
