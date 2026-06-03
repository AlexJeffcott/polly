/**
 * Test-time CSS-modules shim for polly-ui mutation testing.
 *
 * Under `bun test` a `.module.css` default import resolves to the file's
 * path *string* — there is no CSS-modules loader — so `classes["foo"]`
 * is `undefined` and every primitive renders an empty `class` attribute.
 * That makes all the class-*selection* logic (Button's tier/color/size
 * mapping, Text's tone/size classes, etc.) invisible to a render test,
 * and therefore unkillable by mutation testing.
 *
 * Importing this module first registers a Bun loader that makes a
 * `.module.css` default export a proxy where `classes[key] === key`.
 * It is a faithful double: production maps each key to a distinct hashed
 * class, the proxy maps each key to its own name — distinct per key, so
 * "which class did the branch pick" becomes observable. An empty-string
 * key (what Stryker's StringLiteral mutator produces) still returns the
 * empty string, which `parts.filter(Boolean)` strips exactly as a
 * missing production class would be.
 *
 * Import side-effect only, guarded so repeated imports across test files
 * register the plugin once.
 */

import { plugin } from "bun";

const FLAG = "__pollyCssModuleKeyShim__";
const g = globalThis as unknown as Record<string, boolean>;

if (!g[FLAG]) {
  g[FLAG] = true;
  plugin({
    name: "polly-css-module-keys",
    setup(build) {
      build.onLoad({ filter: /\.module\.css$/ }, () => ({
        loader: "object",
        exports: {
          default: new Proxy(
            {},
            {
              get: (_target, key) => (typeof key === "string" ? key : undefined),
            }
          ),
        },
      }));
    },
  });
}
