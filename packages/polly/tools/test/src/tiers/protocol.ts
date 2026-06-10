/**
 * The one shared constant between the engine and its subprocess worker.
 *
 * It lives in its own leaf module so the engine never has to *import* the
 * worker (only spawn it by path). If the engine imported the worker, a
 * `splitting: false` bundle would inline the worker's `import.meta.main`
 * self-exec block into the CLI bundle and run it on startup. Keeping the
 * sentinel here avoids that.
 */
export const SENTINEL = "__TIER_RESULT__";
