/**
 * polly#127: resolve a `$meshState` key to its Automerge document id, for
 * the `--snapshot` overlay only.
 *
 * The derivation needs `tweetnacl` and `@automerge/automerge-repo`, both
 * optional peers of @fairfox/polly. A static import would make every
 * `polly visualize` run need them, so this module imports them dynamically
 * and only the snapshot path calls it. The specifiers are bare, so the
 * bundler keeps them external and they are not hoisted into a top-level
 * import of the visualize bundle.
 */

import { deriveDocumentIdWith } from "../../../src/shared/lib/derive-document-id-core";
import { loadToolPackage, VISUALIZE_SNAPSHOT_FEATURE } from "../../tool-deps/src/index.ts";

/** Maps a logical `$meshState` key to the document id the runtime would use. */
export type DocumentIdResolver = (key: string) => string;

/**
 * Load the derivation's primitives. Throws a `MissingToolPackageError`
 * naming every missing package and the command that installs them.
 */
export async function loadDocumentIdResolver(): Promise<DocumentIdResolver> {
  const nacl = await loadToolPackage(
    "tweetnacl",
    VISUALIZE_SNAPSHOT_FEATURE,
    () => import("tweetnacl")
  );
  const { interpretAsDocumentId } = await loadToolPackage(
    "@automerge/automerge-repo",
    VISUALIZE_SNAPSHOT_FEATURE,
    () => import("@automerge/automerge-repo/slim")
  );
  const primitives = { hash: nacl.default.hash, interpretAsDocumentId };
  return (key) => String(deriveDocumentIdWith(primitives, key));
}
