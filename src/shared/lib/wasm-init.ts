/**
 * Eagerly initialise Automerge's WebAssembly runtime by pointing the library
 * at the raw `.wasm` file shipped in `@automerge/automerge`.
 *
 * The `import.meta.url` pattern below is recognised by every modern bundler
 * (Bun, Vite, webpack 5+, esbuild) as an asset reference: the `.wasm` gets
 * copied into the consumer's output alongside the JavaScript, and the URL is
 * rewritten to point at the copied file. `initializeWasm` then fetches and
 * instantiates it at runtime. That keeps the WebAssembly out of the JavaScript
 * bundle entirely — no megabyte-scale base64 string inlined per subpath — and
 * lets the browser parse the JS and stream-compile the `.wasm` in parallel.
 *
 * The top-level `await` makes this module async so any consumer that
 * transitively imports it inherits the "wait for WASM" behaviour through the
 * import graph, without needing an explicit init call.
 */

import wasmPath from "@automerge/automerge/automerge.wasm";
import { initializeWasm } from "@automerge/automerge-repo/slim";

// Bun's file loader returns a relative path; resolving it against the
// current module's URL yields an absolute URL that fetches correctly
// regardless of where the consumer's bundler places the script.
const wasmUrl = new URL(wasmPath, import.meta.url).href;

await initializeWasm(wasmUrl);
