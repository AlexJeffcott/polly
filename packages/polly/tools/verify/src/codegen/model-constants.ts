// The constant sets a generated `.cfg` declares, in one place.
//
// polly#183 is what happens when two callers each keep their own copy. The
// `.cfg` writer emitted a fixed three-element `Contexts` set; the state-space
// estimator modelled `maxTabs + 1` contexts and no send branching at all. The
// prediction missed the run it was predicting by about 10^5, and a subsystem
// that never terminated was reported as ~5,800 states.
//
// Both the writer (`TLAGenerator.addBasicConstants` /
// `addProjectSpecificConstants`) and the estimator read this module, so the two
// cannot drift again without a test noticing.

/**
 * The `Contexts` set the generated `.cfg` assigns.
 *
 * Fixed, and not derived from any config key: the model was written for a
 * browser extension with a background worker, a content script and a popup.
 * `messages.maxContexts` emits a `MaxContexts` constant that the `Contexts`
 * definition does not read.
 */
export const GENERATED_CONTEXTS = ["background", "content", "popup"] as const;

/** `|Contexts|` in every generated spec. */
export const CONTEXT_COUNT = GENERATED_CONTEXTS.length;

/**
 * The subset of `messages` that decides the generated `Tabs` set.
 *
 * Structural rather than `MessageConfig` so the estimator can pass a legacy or
 * adapter config's message block without narrowing it first.
 */
export type TabSetInput = {
  maxTabs?: number | null | undefined;
  maxClients?: number | null | undefined;
  maxRenderers?: number | null | undefined;
  maxWorkers?: number | null | undefined;
  maxContexts?: number | null | undefined;
  tabSymmetry?: boolean | undefined;
};

/**
 * Whether a project-specific bound is declared. The `.cfg` writer narrows the
 * default tab set from `{0, 1}` to `{0}` when one is, on the reading that a
 * project naming workers/renderers/clients is not a multi-tab extension.
 */
function hasProjectConstant(messages: TabSetInput): boolean {
  return (
    messages.maxWorkers !== undefined ||
    messages.maxRenderers !== undefined ||
    messages.maxContexts !== undefined ||
    messages.maxClients !== undefined
  );
}

/**
 * The literal values the generated `.cfg` assigns to `Tabs`, in emission order.
 *
 * Model values (`Tab0`, `Tab1`, …) under `messages.tabSymmetry`; integers
 * otherwise.
 */
export function generatedTabValues(messages: TabSetInput): string[] {
  if (messages.tabSymmetry) {
    const maxTabs = messages.maxTabs ?? 1;
    return Array.from({ length: maxTabs + 1 }, (_, i) => `Tab${i}`);
  }

  if (messages.maxTabs !== undefined && messages.maxTabs !== null) {
    return Array.from({ length: messages.maxTabs + 1 }, (_, i) => String(i));
  }

  return hasProjectConstant(messages) ? ["0"] : ["0", "1"];
}

/** `|Tabs|` for a given message config. */
export function generatedTabCount(messages: TabSetInput): number {
  return generatedTabValues(messages).length;
}

/**
 * `|SUBSET Contexts \ {{}}|` — the non-empty target sets a send may address.
 *
 * `UserNext` quantifies over every one of them, so this multiplies the
 * successor count of a single `SendMessage` step.
 */
export const TARGET_SET_COUNT = 2 ** CONTEXT_COUNT - 1;

/**
 * Distinct successor states of one `SendMessage` step in a generated spec.
 *
 * `UserNext` emits:
 *
 * ```tla
 * \/ \E src \in Contexts : \E targetSet \in (SUBSET Contexts \ {{}}) :
 *    \E tab \in Tabs : \E msgType \in UserMessageTypes :
 *    SendMessage(src, targetSet, tab, msgType) /\ ...
 * ```
 *
 * so a send branches `|Contexts| * (2^|Contexts| - 1) * |Tabs| * |handlers|`
 * ways. `MaxMessages` (`messages.maxInFlight`) is the exponent on it.
 */
export function sendBranchingFactor(handlerCount: number, tabCount: number): number {
  return CONTEXT_COUNT * TARGET_SET_COUNT * tabCount * handlerCount;
}
