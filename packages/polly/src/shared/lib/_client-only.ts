/**
 * _client-only — Phase 1 prototype for the server-side exclusion mechanism
 * the plan calls for under risk #4.
 *
 * The eventual Phase 2 $meshState primitive must not be importable from
 * server-side code: the primitive has no server-side semantics (no
 * decryption keys, no signing identity), and an accidental server import
 * would be a real bug. The plan asked for a "trivial prototype" early in
 * Phase 0 to verify the exclusion mechanism works before the real $meshState
 * needs to rely on it. This file is that prototype.
 *
 * Mechanism: the module evaluates a runtime guard at import time. When the
 * importer's environment lacks `globalThis.window` (i.e. Node, Bun, Deno,
 * any server-side runtime), the import throws a structured error naming
 * the file and pointing at the plan risk. The throw fires during module
 * evaluation, not on first symbol use, so a server-side file that even
 * declares `import "@/shared/lib/_client-only"` will fail loudly.
 *
 * This is a runtime mechanism, not a type-level one. The strong static
 * guarantee — server code cannot even compile against this module — needs
 * either TypeScript project references with a separate server tsconfig
 * that excludes this file, or package.json conditional exports that
 * resolve to a stub on the server side. Both are real build-config
 * changes that touch the rest of the codebase. The plan deferred the
 * type-level enforcement to Phase 2 alongside the actual $meshState
 * machinery, where it becomes load-bearing rather than speculative.
 *
 * Until then, the runtime guard demonstrates that Polly knows how to
 * forbid server imports of a marked module, and the test next to this
 * file proves the guard fires under Bun's server-side runtime.
 */

if (typeof globalThis.window === "undefined") {
  throw new Error(
    "Polly: src/shared/lib/_client-only.ts is a client-only module and cannot be imported from a server-side runtime. " +
      "This module exists as the Phase 1 prototype for plan risk #4 (server-side $meshState exclusion). " +
      "If you are seeing this error from production code, you have an accidental server import of a client-only module. " +
      "If you are seeing it from a test, mock `globalThis.window` before importing."
  );
}

/**
 * A sentinel value the prototype exports so that consumers have something
 * to import. Production code never reads this; the value exists only so
 * the module has a non-empty default export and the runtime guard above
 * has something to gate.
 */
export const clientOnlyMarker = "polly-client-only-prototype";
