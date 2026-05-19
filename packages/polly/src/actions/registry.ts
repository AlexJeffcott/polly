/**
 * Action registry types.
 *
 * An action registry is a plain object mapping action names to handlers.
 * Handlers receive a typed context with the app's stores, the DOM event,
 * the element carrying `data-action`, and parsed `data-action-*` data.
 * Handlers return void or a Promise for async work.
 *
 * Users compose registries by spreading partial registries (e.g. from
 * `createForm`) into one central object:
 *
 *   const ACTION_REGISTRY: ActionRegistry<RootStore> = {
 *     ...teamForm.actions,
 *     ...projectForm.actions,
 *     'app:theme:toggle': ({ stores }) => { ... },
 *   }
 */

export type ActionContext<TStores> = {
  stores: TStores;
  event: Event;
  element: HTMLElement;
  data: Record<string, string>;
};

export type ActionHandler<TStores> = (ctx: ActionContext<TStores>) => void | Promise<void>;

export type ActionRegistry<TStores> = Record<string, ActionHandler<TStores>>;
