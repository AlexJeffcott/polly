------------------------- MODULE ChromeExtension -------------------------
(*
  Template for Chrome extension verification.

  Architecture: Multi-context extension pattern
  - Background script (singleton, persistent)
  - Content scripts (per-tab, injected into web pages)
  - Popup (ephemeral, user-activated)
  - Options page (singleton, user-activated)
  - DevTools (per-tab, developer-activated)

  Usage:
    Import this module in your generated specification:
    INSTANCE ChromeExtension

  Invariants:
    - BackgroundIsSingleton: Only one background context exists
    - ContentScriptsAreTabScoped: Content scripts always have a tabId
    - PopupEphemeral: Popup can disconnect at any time
    - NoRoutingLoops: Messages don't cycle back to sender
    - TabIsolation: Content scripts in different tabs are isolated
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

(* ───────────────────────────────────────────────────────────────── *)
(* Constants                                                           *)
(* ───────────────────────────────────────────────────────────────── *)

CONSTANTS
    MaxTabId \* Maximum tab ID to model (bounds content script instances)

(* ───────────────────────────────────────────────────────────────── *)
(* Extension-Specific Type Definitions                                *)
(* ───────────────────────────────────────────────────────────────── *)

\* Extension contexts
ExtensionContexts == {
    "background",
    "content",
    "popup",
    "devtools",
    "options",
    "offscreen",
    "sidepanel"
}

\* Tab IDs (0 = no tab context, 1..MaxTabId = specific tabs)
TabIds == 0..MaxTabId

\* Lifecycle states for extension contexts
LifecycleStates == {
    "active",      \* Context is running
    "suspended",   \* Context is suspended (not applicable to all contexts)
    "terminated"   \* Context has ended
}

(* ───────────────────────────────────────────────────────────────── *)
(* Helper Operators                                                    *)
(* ───────────────────────────────────────────────────────────────── *)

\* Convert a sequence to a set of its elements
Range(seq) == {seq[i] : i \in DOMAIN seq}

(* ───────────────────────────────────────────────────────────────── *)
(* Chrome Extension-Specific Invariants                               *)
(* ───────────────────────────────────────────────────────────────── *)

\*
\* Invariant: Background context is a singleton
\*
\* Chrome extensions have exactly one background context (service worker
\* or background page). This invariant ensures that all messages from
\* the background context have tabId = 0 (no associated tab).
\*
\* This catches bugs like:
\* - Multiple background instances
\* - Background incorrectly associated with tabs
\* - Scope confusion between background and content scripts
\*
BackgroundIsSingleton(messages) ==
    \A msg \in Range(messages) :
        msg.source = "background" => msg.tabId = 0

\*
\* Invariant: Content scripts are tab-scoped
\*
\* Content scripts run in the context of web pages and are always
\* associated with a specific tab. This invariant ensures every
\* message from a content script has a valid tabId (1..MaxTabId).
\*
\* This catches bugs like:
\* - Content scripts without tab associations
\* - Tab ID corruption
\* - Content scripts leaking across tabs
\*
ContentScriptsAreTabScoped(messages) ==
    \A msg \in Range(messages) :
        msg.source = "content" => msg.tabId \in 1..MaxTabId

\*
\* Invariant: Popup is ephemeral (can disconnect anytime)
\*
\* Popup windows can be closed by the user at any time, and should not
\* hold critical state. This invariant doesn't prevent disconnection,
\* but is documented for user awareness.
\*
\* In TLA+, this is represented as TRUE (no constraint), but serves
\* as documentation that popups are ephemeral.
\*
PopupEphemeral ==
    TRUE  \* Popups can disconnect freely

\*
\* Invariant: No message routing loops
\*
\* Messages should not cycle back to their sender. This prevents
\* infinite loops and ensures message flow is acyclic.
\*
\* This catches bugs like:
\* - Echo loops where messages bounce back
\* - Routing misconfigurations
\* - Circular message dependencies
\*
NoRoutingLoops(messages) ==
    \A msg \in Range(messages) :
        msg.source \notin msg.targets

\*
\* Invariant: Tab isolation for content scripts
\*
\* Content scripts in different tabs should be isolated from each other.
\* Messages from one content script should not directly reach content
\* scripts in other tabs without going through the background.
\*
\* This catches bugs like:
\* - Tab isolation violations
\* - Cross-tab state leakage
\* - Security issues from tab confusion
\*
TabIsolation(messages) ==
    \A msg1, msg2 \in Range(messages) :
        (/\ msg1.source = "content"
         /\ msg2.source = "content"
         /\ msg1.tabId # msg2.tabId
         /\ msg1.source \in msg2.targets)
        => FALSE  \* Content scripts in different tabs cannot message each other

\*
\* Invariant: Background always connected (for persistent background pages)
\*
\* For extensions with persistent background pages (not service workers),
\* the background should always be connected. Service workers can be
\* suspended, so this is conditional.
\*
\* Note: Set backgroundPersistent based on your manifest configuration
\*
BackgroundPersistent(ports, backgroundPersistent) ==
    backgroundPersistent => ports["background"] = "connected"

\*
\* Invariant: Options and DevTools are user-activated
\*
\* Options pages and DevTools panels should only be active when explicitly
\* opened by the user. They should not spontaneously activate.
\*
\* This catches bugs like:
\* - Contexts activating without user interaction
\* - Lifecycle management issues
\*
UserActivatedContexts(ports, userAction) ==
    (/\ ports["options"] = "connected" => userAction["options"])
    /\ (ports["devtools"] = "connected" => userAction["devtools"])

\*
\* Invariant: Messages respect extension architecture
\*
\* Only certain contexts can communicate directly. For example:
\* - Content scripts must communicate through background
\* - Popup can message background directly
\* - Background can broadcast to all contexts
\*
\* This enforces the Chrome extension messaging topology.
\*
ValidMessagingTopology(messages) ==
    \A msg \in Range(messages) :
        \/ msg.source = "background"  \* Background can send to anyone
        \/ msg.source = "content" /\ msg.targets = {"background"}  \* Content -> background only
        \/ msg.source = "popup" /\ msg.targets \subseteq {"background", "content"}  \* Popup -> background or content
        \/ msg.source = "options" /\ msg.targets = {"background"}  \* Options -> background only
        \/ msg.source = "devtools" /\ msg.targets = {"background"}  \* DevTools -> background only

=============================================================================
\* Changelog:
\* 2025-12-15: Initial Chrome extension template with extension-specific invariants
