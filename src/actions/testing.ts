/**
 * Testing helpers for action handlers.
 *
 * Handlers are plain functions taking an ActionContext; these helpers
 * build the context pieces without jsdom. For full-DOM tests use the
 * browser harness at `@fairfox/polly/test/browser`.
 */

import type {
  ActionContext,
  ActionHandler,
  ActionRegistry,
} from "./registry.ts";

/**
 * Build a mock element that satisfies ActionContext.element.
 * Only the surface a handler is likely to touch is populated.
 */
export function createMockElement(
  attrs: Record<string, string> = {},
  tagName = "DIV",
): HTMLElement {
  const attrMap = new Map(Object.entries(attrs));
  const el = {
    tagName,
    nodeType: 1,
    getAttribute: (name: string) => attrMap.get(name) ?? null,
    setAttribute: (name: string, value: string) => {
      attrMap.set(name, value);
    },
    hasAttribute: (name: string) => attrMap.has(name),
    removeAttribute: (name: string) => {
      attrMap.delete(name);
    },
    attributes: Array.from(attrMap.entries()).map(([name, value]) => ({
      name,
      value,
    })),
  } as unknown as HTMLElement;
  return el;
}

/** Build a minimal submit-like event wrapping a `<form>` FormData payload. */
export function createMockSubmitEvent(
  form: HTMLFormElement | Record<string, string>,
): Event {
  const isReal =
    typeof HTMLFormElement !== "undefined" && form instanceof HTMLFormElement;
  const target = isReal
    ? (form as HTMLFormElement)
    : createMockFormElement(form as Record<string, string>);
  let defaultPrevented = false;
  return {
    type: "submit",
    target,
    currentTarget: target,
    preventDefault() {
      defaultPrevented = true;
    },
    stopPropagation() {},
    get defaultPrevented() {
      return defaultPrevented;
    },
  } as unknown as Event;
}

function createMockFormElement(fields: Record<string, string>): HTMLFormElement {
  return {
    nodeType: 1,
    tagName: "FORM",
    elements: Object.entries(fields).map(([name, value]) => ({
      name,
      value,
    })),
  } as unknown as HTMLFormElement;
}

/**
 * Shallow-merged partial stores. Callers typically pass signal-backed fakes.
 */
export function createMockStores<TStores extends object>(
  partial: Partial<TStores> = {},
): TStores {
  return partial as TStores;
}

/**
 * Run a handler in isolation. Useful for unit-testing action logic without
 * wiring the full document event delegation.
 */
export async function runAction<TStores>(
  registry: ActionRegistry<TStores>,
  action: string,
  ctx: Partial<ActionContext<TStores>> & { stores: TStores },
): Promise<void> {
  const handler: ActionHandler<TStores> | undefined = registry[action];
  if (!handler) {
    throw new Error(`No handler registered for action "${action}"`);
  }
  const fullCtx: ActionContext<TStores> = {
    stores: ctx.stores,
    event: ctx.event ?? new Event("click"),
    element: ctx.element ?? createMockElement(),
    data: ctx.data ?? {},
  };
  await handler(fullCtx);
}
