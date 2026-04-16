/**
 * Test preload — suppress known automerge-repo/xstate "Cycle detected"
 * errors that leak as unhandled exceptions when multiple Repos coexist
 * across test files running in the same process.
 *
 * The cycle is internal to xstate's raise-action processing inside
 * automerge-repo's DocHandle state machine and does not affect test
 * correctness. xstate throws the error via setTimeout(() => { throw err }),
 * so the only way to intercept it is to wrap setTimeout.
 */

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
