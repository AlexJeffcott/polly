/**
 * Test preload — two process-wide concerns that must be set up before any
 * test file imports a component.
 *
 * 1. The CSS-modules key-proxy shim. Under `bun test` a `.module.css`
 *    default import resolves to the file path, so `classes[key]` is
 *    undefined and every class-name assertion is invisible. The shim
 *    registers a Bun loader that makes `classes[key] === key`. Loading it
 *    here, in the preload, means the loader is active before the first
 *    component import in the process — otherwise the first test file to
 *    import a component (in any hand-picked subset) caches it with string
 *    classes and later files that assert class tokens fail. The shim is
 *    guarded by a global flag, so the existing per-file imports are no-ops.
 *
 * 2. Suppressing known automerge-repo/xstate "Cycle detected" errors that
 *    leak as unhandled exceptions when multiple Repos coexist across test
 *    files in the same process. The cycle is internal to xstate's
 *    raise-action processing inside automerge-repo's DocHandle state
 *    machine and does not affect test correctness. xstate throws via
 *    setTimeout(() => { throw err }), so the only interception point is to
 *    wrap setTimeout.
 */

import "./unit/helpers/css-module-keys.ts";

const _origSetTimeout = globalThis.setTimeout;

// @ts-expect-error — wrapping setTimeout to intercept xstate cycle errors
globalThis.setTimeout = function patchedSetTimeout(fn: unknown, ...args: unknown[]) {
  if (typeof fn === "function") {
    const wrapped = (...callArgs: unknown[]) => {
      try {
        return fn(...callArgs);
      } catch (err) {
        if (err instanceof Error && err.message === "Cycle detected") {
          return;
        }
        throw err;
      }
    };
    // @ts-expect-error — pass-through to original setTimeout
    return _origSetTimeout(wrapped, ...args);
  }
  // @ts-expect-error — pass-through to original setTimeout
  return _origSetTimeout(fn, ...args);
};
