/**
 * Install or remove a global a test stubs (`chrome`, `BroadcastChannel`,
 * `window`). `Reflect` writes the property without claiming a type for
 * `globalThis`. Replaces `(globalThis as unknown as { x: unknown }).x = v`.
 */
export function setGlobal(name: string, value: unknown): void {
  Reflect.set(globalThis, name, value);
}

export function clearGlobals(...names: string[]): void {
  for (const name of names) Reflect.deleteProperty(globalThis, name);
}
