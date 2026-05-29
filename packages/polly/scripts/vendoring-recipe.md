# Vendoring polly (mesh-free / UI-free / test-free)

`vendor-polly.sh` copies a slice of polly's source into another codebase,
keeping the core framework plus the `verify` and `visualize` tools, and
dropping the UI, the mesh runtime, the Chrome-extension UI contexts, all
tests, and the `init`/`quality`/`test` tooling.

The result installs with four runtime dependencies and **zero**
`@automerge/*` / `ws` / `tweetnacl` / `werift` / `@roamhq/wrtc` / `marked` /
`dompurify`. It builds end-to-end (`bun run build:lib`, including `.d.ts`
generation) on its own.

## Usage

```bash
scripts/vendor-polly.sh <source-polly-pkg-dir> <target-dir> [--check]
```

- `<source-polly-pkg-dir>` — path to polly's `packages/polly` (must contain
  `src/` and `tools/verify/`).
- `<target-dir>` — where the vendored copy is written (created if absent).
- `--check` — after vendoring, run `bun install` + `bunx tsc --noEmit` in the
  target to verify it builds.

```bash
# Vendor into a consumer repo, then build
scripts/vendor-polly.sh ../polly/packages/polly ./vendor/polly --check
cd ./vendor/polly && bun install && bun run build:lib
```

The script is idempotent: `rsync --delete` restores pristine source on every
run, then re-applies the trims, so re-running produces an identical tree. It
prints warnings if polly's layout has drifted (e.g. an expected import is no
longer where the redirect expects it), so a future polly version cannot
silently mis-vendor.

## What is kept

- **Core framework** — `state`, `resource`, `message-bus`, `background`,
  `message-router`, `adapters`, `errors`, `guards`, `types`, `actions`,
  `client`.
- **Elysia integration** — with the mesh `peerRepo` plugin trimmed out.
- **`verify`** — formal verification, plus its `analysis` extraction engine
  and the Stryker ignorer.
- **`visualize`** — architecture diagrams, with the mesh `--snapshot` overlay
  neutralised.

## What is removed

UI (`src/polly-ui`), the mesh runtime (28 `src/shared/lib` files plus
`mesh.ts` / `mesh-node.ts` / `peer.ts` / `elysia/peer-repo-plugin.ts`),
Chrome-extension UI contexts (`content`, `devtools`, `offscreen`, `options`,
`page`, `popup`), the `init` / `quality` / `test` tools, `verify`'s
test-fixture projects, the mesh TLA+ specs (keeping `MessageRouter`), and
every `__tests__/` directory and `*.test.ts` file.

## Why the dependency boundary lands where it does

The keep set is the transitive closure of relative imports from the kept
entry points. Two couplings are not obvious and are why pure file deletion is
insufficient:

1. **`src/elysia/index.ts` re-exports the `peerRepo` plugin**, which pulls
   `peer-repo-server` → `@automerge`. The script removes that one re-export
   line so the `./elysia` export stays mesh-free.

2. **`visualize`'s `--snapshot` overlay** (polly#127) imports
   `MeshClientPeerStateSnapshot` (type-only, from `mesh-client.ts`) in three
   files and `deriveDocumentId` (a runtime value, from
   `derive-document-id.ts`) in `structurizr.ts`. `deriveDocumentId` itself
   pulls `@automerge/automerge-repo/slim`. The script deletes both leaf
   modules and redirects all five imports onto a generated stub
   (`tools/visualize/src/_vendor-mesh-stub.ts`): loose snapshot types plus a
   `deriveDocumentId` that throws. The overlay code still compiles; invoking
   `visualize --snapshot` throws a clear "unavailable in mesh-free build"
   error rather than failing to compile.

Everything else partitions cleanly — `verify`, `analysis`, and `quality` have
no `src/` dependencies at all; they operate on the consumer's code via
ts-morph.

## Gotchas the build surfaces (already handled by the script)

These were found by actually building the vendored tree, not by reading the
import graph — keep them in mind if you change the keep set:

- **`@types/chrome` is required**, not optional. The core Chrome adapters
  (`shared/adapters/chrome/*`, `storage-adapter.ts`, `sync-adapter.ts`,
  `messages.ts`) reference the `chrome` global, so declaration generation
  fails without it. It is in the trimmed `devDependencies`.
- **`tools/verify/src/config.ts` must be a build entry point** — it is the
  target of the `./verify` subpath export. The import closure misses it
  because nothing in the kept tree imports it; only the `package.json`
  `exports` map references it.
- **Runtime assets the closure cannot see** must be kept by path:
  `tools/verify/Dockerfile` (the runner builds the TLA+ image from it) and
  `tools/verify/specs/tla/MessageRouter.tla` + `.cfg` (copied into the
  consumer's spec dir; verification fails without it).

## Limitations

- `polly build` / `dev` / `test` / `quality` / `init` subcommands are
  unavailable — their CLIs and `scripts/` are not vendored. The `polly`
  dispatcher fails gracefully per command. To restore the extension build,
  copy `scripts/build-extension.ts` and its dependencies.
- If you retain the Chrome-extension background helpers (`api-client.ts`,
  `context-menu.ts`, `offscreen-manager.ts` — deleted by default), edit the
  deletion step of the script.
- `@babel/parser` / `@babel/traverse` may be needed in `devDependencies` if
  `tools/analysis` uses them; the build will tell you.
