/**
 * Store base + Preact context.
 *
 * `createStore` is a thin convention-enforcer: a typed bag of signals
 * plus methods. Apps use it to define domain stores whose only public
 * mutation surface is named methods (actions call them; components read
 * signals and dispatch actions). No cleverness — a named pattern more
 * than a library.
 *
 * `StoreProvider` + `useStores` wire the stores bag into Preact context
 * so components and the delegation runtime can reach it via a single hook.
 */

import type { ComponentChildren } from "preact";
import { createContext } from "preact";
import { useContext } from "preact/hooks";

/**
 * Identity helper; exists so domain stores have a canonical creation
 * call even though the bag itself is a plain object. Centralising here
 * lets us hang additional behaviour off the call site later (debug
 * instrumentation, devtools) without a migration.
 */
export function createStore<T extends object>(init: T): T {
  return init;
}

const StoreContext = createContext<unknown>(null);

export type StoreProviderProps<TStores> = {
  children: ComponentChildren;
  stores: TStores;
};

export function StoreProvider<TStores>({
  children,
  stores,
}: StoreProviderProps<TStores>) {
  return (
    <StoreContext.Provider value={stores}>{children}</StoreContext.Provider>
  );
}

export function useStores<TStores>(): TStores {
  const ctx = useContext(StoreContext) as unknown as TStores | null;
  if (ctx === null) {
    throw new Error("useStores must be used within a StoreProvider");
  }
  return ctx;
}
