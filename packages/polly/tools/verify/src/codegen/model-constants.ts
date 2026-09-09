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
 * The `Contexts` set a config that declares none gets.
 *
 * Three names chosen when polly modelled a browser extension with a background
 * worker, a content script and a popup. It stays the default so a config
 * written before polly#185 generates the same spec it did.
 */
export const DEFAULT_CONTEXTS = ["background", "content", "popup"] as const;

/**
 * The subset of a verification config that decides the generated `Contexts`
 * set.
 *
 * Structural rather than `VerificationConfig` so the estimator can pass a
 * legacy or adapter config without narrowing it first.
 */
export type ContextSetInput = {
  contexts?: readonly string[] | null | undefined;
};

/** A TLA+ model value: a letter or underscore, then letters, digits, underscores. */
export const CONTEXT_NAME_PATTERN = /^[A-Za-z_][A-Za-z0-9_]*$/;

/**
 * Make a declared context name safe to emit as a TLA+ model value.
 *
 * The rule `TLAGenerator.sanitizeIdentifier` applies to mesh doc ids
 * (polly#117): every character that is not a letter, digit or underscore
 * becomes an underscore. A name whose sanitised form is still not an
 * identifier (`"1st"`, `""`) is rejected at config validation rather than
 * mangled here.
 */
export function sanitizeContextName(name: string): string {
  return name.replace(/[^A-Za-z0-9_]/g, "_");
}

/** Whether the config declares its own context set (polly#185). */
export function hasDeclaredContexts(config?: ContextSetInput | null): boolean {
  const declared = config?.contexts;
  return Array.isArray(declared) && declared.length > 0;
}

/**
 * The literal values the generated `.cfg` assigns to `Contexts`.
 *
 * `config.contexts` when declared, sanitised for emission; `DEFAULT_CONTEXTS`
 * otherwise. Nothing in the generated `.tla` or in `MessageRouter.tla` names a
 * member of the set — every use is a quantifier or a function domain — so this
 * one line decides `|Contexts|` for the whole model (polly#185).
 */
export function resolveContexts(config?: ContextSetInput | null): string[] {
  if (!hasDeclaredContexts(config)) return [...DEFAULT_CONTEXTS];
  return (config?.contexts as readonly string[]).map(sanitizeContextName);
}

/**
 * `|SUBSET Contexts \ {{}}|` — the non-empty target sets a send may address.
 *
 * `UserNext` quantifies over every one of them, so this multiplies the
 * successor count of a single `SendMessage` step.
 */
export function targetSetCount(contexts: readonly string[]): number {
  return 2 ** contexts.length - 1;
}

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
 * ways. `MaxMessages` (`messages.maxInFlight`) is the exponent on it — which is
 * why the context set is the cheapest term to cut (polly#185).
 */
export function sendBranchingFactor(
  handlerCount: number,
  tabCount: number,
  contexts: readonly string[]
): number {
  return contexts.length * targetSetCount(contexts) * tabCount * handlerCount;
}
