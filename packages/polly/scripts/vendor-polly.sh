#!/usr/bin/env bash
#
# vendor-polly.sh — vendor a mesh-free / UI-free / test-free slice of polly
# into another codebase.
#
# Copies polly's source (src/, tools/, cli/) into a target directory, then
# removes the UI, mesh, and test surfaces and keeps only:
#   - the core framework (state, resource, message-bus, background,
#     message-router, adapters, errors, guards, types, actions, client)
#   - the elysia integration (with the mesh peerRepo plugin trimmed out)
#   - the `verify` tool (formal verification) + its analysis engine + stryker
#   - the `visualize` tool (with the mesh --snapshot overlay neutralised)
#   - the `quality` tool (conformance checks, exported as @fairfox/polly/quality)
#
# The result has zero @automerge/* / ws / tweetnacl / werift / wrtc / marked /
# dompurify dependencies. The one runtime coupling — deriveDocumentId, used by
# the visualize --snapshot overlay — is replaced with a throwing stub, so the
# overlay compiles but reports "unavailable" if invoked.
#
# The script is idempotent: re-running against an already-vendored target is a
# no-op (deletes already gone, import redirects already applied, generated
# files overwritten identically).
#
# Usage:
#   scripts/vendor-polly.sh <source-polly-pkg-dir> <target-dir> [--check]
#
#   <source-polly-pkg-dir>  path to polly's packages/polly (must contain
#                           src/ and tools/verify/)
#   <target-dir>            where the vendored copy is written (created if
#                           absent; existing files are overwritten/removed)
#   --check                 after vendoring, run `bun install` + `bunx tsc
#                           --noEmit` in the target to verify it builds
#
set -euo pipefail

# ----------------------------------------------------------------------------
# args + logging
# ----------------------------------------------------------------------------
CHECK=0
ARGS=()
for a in "$@"; do
  case "$a" in
    --check) CHECK=1 ;;
    -*) echo "unknown flag: $a" >&2; exit 2 ;;
    *) ARGS+=("$a") ;;
  esac
done

if [ "${#ARGS[@]}" -ne 2 ]; then
  echo "usage: $0 <source-polly-pkg-dir> <target-dir> [--check]" >&2
  exit 2
fi

SRC="$(cd "${ARGS[0]}" 2>/dev/null && pwd || true)"
TARGET_RAW="${ARGS[1]}"

c_blue=$'\033[34m'; c_yellow=$'\033[33m'; c_green=$'\033[32m'; c_dim=$'\033[2m'; c_off=$'\033[0m'
log()  { printf '%s•%s %s\n' "$c_blue" "$c_off" "$1"; }
warn() { printf '%s⚠ %s%s\n' "$c_yellow" "$1" "$c_off"; }
ok()   { printf '%s✓ %s%s\n' "$c_green" "$1" "$c_off"; }

if [ -z "$SRC" ] || [ ! -d "$SRC/src" ] || [ ! -d "$SRC/tools/verify" ]; then
  echo "error: '${ARGS[0]}' is not a polly packages/polly dir (need src/ and tools/verify/)" >&2
  exit 1
fi

mkdir -p "$TARGET_RAW"
TARGET="$(cd "$TARGET_RAW" && pwd)"
log "source: $SRC"
log "target: $TARGET"

# ----------------------------------------------------------------------------
# 1. copy source trees + curated root files
# ----------------------------------------------------------------------------
log "copying src/, tools/, cli/ …"
# rsync excludes the heavy/irrelevant bits up front; the deletes below remove
# the rest. --delete keeps re-runs clean for these three trees.
for tree in src tools cli; do
  rsync -a --delete \
    --exclude='node_modules' \
    --exclude='dist' \
    --exclude='.git' \
    "$SRC/$tree/" "$TARGET/$tree/"
done

# Curated root files (only if present in source).
for f in tsconfig.json bunfig.toml biome.json README.md LICENSE bun-env.d.ts; do
  [ -f "$SRC/$f" ] && cp "$SRC/$f" "$TARGET/$f"
done
ok "source copied"

# ----------------------------------------------------------------------------
# 2. deletions — UI, chrome-extension contexts, dropped tooling, mesh, tests
# ----------------------------------------------------------------------------
del() { for p in "$@"; do rm -rf "$TARGET/$p"; done; }

log "deleting UI + extension-context dirs …"
del src/polly-ui src/assets src/content src/devtools src/offscreen src/options src/page src/popup

# tools/quality is KEPT: it is a self-contained textual scanner (bun + node:*
# only — no UI, mesh, or framework-runtime imports) and is exported as
# `@fairfox/polly/quality` so consumers run the same conformance checks Polly
# enforces on itself, rather than re-implementing them. Its tests are still
# stripped by the generic test deletion below.
#
# tools/gallery follows src/polly-ui out: it renders polly-ui specimens and
# imports `src/polly-ui` directly, so it cannot type-check once the UI is
# removed. It is unexported and node-unbuilt, so dropping it is invisible to
# consumers (and without this the slice's own --check fails tsc).
log "deleting dropped tooling (init, test, gallery) …"
del tools/init tools/test tools/gallery

log "deleting top-level mesh/extension entry files …"
del src/manifest.json src/wasm.d.ts src/mesh.ts src/mesh-node.ts src/peer.ts

log "deleting mesh substrate in src/shared/lib/ …"
for f in \
  _client-only blob-cache blob-store blob-store-impl blob-transfer \
  crdt-specialised crdt-state derive-document-id encryption keyring-storage \
  mesh-client mesh-diagnostics mesh-network-adapter mesh-signaling-client \
  mesh-state mesh-webrtc-adapter migrate-primitive pairing \
  peer-relay-adapter peer-repo-server peer-state primitive-registry \
  revocation revocation-summary schema-version signing sweep-sealed \
  sync-fragment wasm-init
do
  del "src/shared/lib/$f.ts"
done

log "deleting mesh integration + orphan files …"
del src/elysia/peer-repo-plugin.ts
del tools/verify/src/adapters/registry.ts

# verify's test-fixture consumer projects (contain mesh code; no runtime refs)
log "deleting verify test-project fixtures …"
del tools/verify/test-projects

# Background helpers not reachable from the public API. Keep these only if you
# target Chrome extensions AND call them directly — comment out to retain.
log "deleting unreferenced background helpers …"
del src/background/api-client.ts src/background/context-menu.ts src/background/offscreen-manager.ts

# Mesh TLA+ models used only by verify's mesh seed-race guard (warns + skips
# when absent). MessageRouter.{tla,cfg} is REQUIRED and kept.
log "deleting mesh TLA+ specs (keeping MessageRouter) …"
del tools/verify/specs/tla/MeshSeed.tla tools/verify/specs/tla/MeshSeed.cfg
del tools/verify/specs/tla/MeshState.tla tools/verify/specs/tla/MeshState.cfg
del tools/verify/specs/tla/PeerState.tla tools/verify/specs/tla/PeerState.cfg
del tools/verify/specs/Dockerfile tools/verify/specs/docker-compose.yml

log "deleting all tests (__tests__ dirs + *.test.ts) …"
find "$TARGET" -type d -name '__tests__' -prune -exec rm -rf {} + 2>/dev/null || true
find "$TARGET" -type f \( -name '*.test.ts' -o -name '*.test.tsx' \) -delete 2>/dev/null || true
ok "deletions complete"

# ----------------------------------------------------------------------------
# 3. mesh-free stub for the visualize overlay
# ----------------------------------------------------------------------------
log "writing mesh-free visualize stub …"
cat > "$TARGET/tools/visualize/src/_vendor-mesh-stub.ts" <<'STUB'
/**
 * Mesh-free stubs — generated by vendor-polly.sh.
 *
 * The mesh runtime (src/shared/lib/mesh-client.ts) and derive-document-id.ts
 * were removed when polly was vendored without mesh support. The
 * `polly visualize --snapshot` overlay (polly#127) visualises live mesh
 * sync-state and is therefore unavailable in this build: the overlay code
 * still compiles against the loose types below, but deriveDocumentId throws
 * if it is ever invoked.
 *
 * If `bunx tsc --noEmit` reports a type mismatch against the overlay code,
 * loosen the fields below (the feature is inert, so precision is optional).
 */

export interface MeshClientHandleSnapshot {
  peerDocumentStatus?: string | undefined;
  [key: string]: unknown;
}

export interface MeshClientPeerStateSnapshot {
  localPeerId: string;
  knownPeerIds: string[];
  presentPeerIds: string[];
  peers: Array<{
    id?: string;
    peerId?: string;
    isLocal?: boolean;
    slot?: { handles?: Record<string, MeshClientHandleSnapshot> } | undefined;
    [key: string]: unknown;
  }>;
  [key: string]: unknown;
}

export function deriveDocumentId(_key: string): string {
  throw new Error(
    "polly was vendored without mesh support: `visualize --snapshot` (mesh overlay) is unavailable",
  );
}
STUB
ok "stub written"

# ----------------------------------------------------------------------------
# 4. redirect the four mesh-leaf imports onto the stub (idempotent)
# ----------------------------------------------------------------------------
redirect() {
  # redirect <file> <from-specifier> <to-specifier>
  local file="$TARGET/$1" from="$2" to="$3"
  if [ ! -f "$file" ]; then warn "skip (missing): $1"; return; fi
  if grep -q -- "$from" "$file"; then
    sed "s|$from|$to|g" "$file" > "$file.vendortmp" && mv "$file.vendortmp" "$file"
    log "redirected '$from' -> '$to' in $1"
  elif grep -q -- "$to" "$file"; then
    log "already redirected: $1"
  else
    warn "import '$from' not found in $1 — polly layout may have changed; verify manually"
  fi
}

log "redirecting visualize mesh imports onto the stub …"
redirect tools/visualize/src/cli.ts               "../../../src/shared/lib/mesh-client"        "./_vendor-mesh-stub"
redirect tools/visualize/src/mesh-snapshot.ts     "../../../src/shared/lib/mesh-client"        "./_vendor-mesh-stub"
redirect tools/visualize/src/codegen/structurizr.ts "../../../../src/shared/lib/mesh-client"     "../_vendor-mesh-stub"
redirect tools/visualize/src/codegen/structurizr.ts "../../../../src/shared/lib/derive-document-id" "../_vendor-mesh-stub"
redirect tools/visualize/src/types/structurizr.ts "../../../../src/shared/lib/mesh-client"     "../_vendor-mesh-stub"
ok "imports redirected"

# ----------------------------------------------------------------------------
# 5. trim the elysia peerRepo re-export (severs core -> automerge)
# ----------------------------------------------------------------------------
log "trimming elysia peerRepo re-export …"
ELYSIA="$TARGET/src/elysia/index.ts"
if [ -f "$ELYSIA" ]; then
  if grep -q 'from "./peer-repo-plugin"' "$ELYSIA"; then
    grep -v 'from "./peer-repo-plugin"' "$ELYSIA" > "$ELYSIA.vendortmp" && mv "$ELYSIA.vendortmp" "$ELYSIA"
    ok "removed peerRepo re-export from src/elysia/index.ts"
  else
    log "elysia peerRepo re-export already absent"
  fi
else
  warn "src/elysia/index.ts missing — skipping elysia trim"
fi

# ----------------------------------------------------------------------------
# 6. trimmed package.json
# ----------------------------------------------------------------------------
log "writing trimmed package.json …"
cat > "$TARGET/package.json" <<'PKG'
{
  "name": "@fairfox/polly",
  "version": "0.0.0-vendored",
  "private": true,
  "type": "module",
  "description": "Vendored polly: core framework + verify + visualize (no UI, mesh, or tests)",
  "main": "dist/index.js",
  "module": "dist/index.js",
  "types": "dist/index.d.ts",
  "bin": { "polly": "./dist/cli/polly.js" },
  "exports": {
    ".":                { "import": "./dist/src/index.js",                      "types": "./dist/index.d.ts" },
    "./state":          { "import": "./dist/src/shared/lib/state.js",           "types": "./dist/shared/lib/state.d.ts" },
    "./resource":       { "import": "./dist/src/shared/lib/resource.js",        "types": "./dist/shared/lib/resource.d.ts" },
    "./message-bus":    { "import": "./dist/src/shared/lib/message-bus.js",     "types": "./dist/shared/lib/message-bus.d.ts" },
    "./background":     { "import": "./dist/src/background/index.js",           "types": "./dist/background/index.d.ts" },
    "./message-router": { "import": "./dist/src/background/message-router.js",  "types": "./dist/background/message-router.d.ts" },
    "./adapters":       { "import": "./dist/src/shared/adapters/index.js",      "types": "./dist/shared/adapters/index.d.ts" },
    "./errors":         { "import": "./dist/src/shared/lib/errors.js",          "types": "./dist/shared/lib/errors.d.ts" },
    "./guards":         { "import": "./dist/src/shared/lib/guards.js",          "types": "./dist/src/shared/lib/guards.d.ts" },
    "./types":          { "import": "./dist/src/shared/types/messages.js",      "types": "./dist/shared/types/messages.d.ts" },
    "./actions":        { "import": "./dist/src/actions/index.js",              "types": "./dist/src/actions/index.d.ts" },
    "./client":         { "import": "./dist/src/client/index.js",               "types": "./dist/src/client/index.d.ts" },
    "./elysia":         { "import": "./dist/src/elysia/index.js",               "types": "./dist/src/elysia/index.d.ts" },
    "./verify":         { "import": "./dist/tools/verify/src/config.js",        "types": "./dist/tools/verify/src/config.d.ts" },
    "./stryker":        { "import": "./dist/tools/verify/src/stryker/index.js", "types": "./dist/tools/verify/src/stryker/index.d.ts" },
    "./quality":        { "import": "./dist/tools/quality/src/index.js",        "types": "./dist/tools/quality/src/index.d.ts" }
  },
  "files": ["dist", "README.md", "LICENSE"],
  "scripts": {
    "build:lib": "bun run build-lib.ts",
    "typecheck": "bunx tsc --noEmit",
    "lint": "biome check .",
    "lint:fix": "biome check --write .",
    "format": "biome format --write ."
  },
  "dependencies": {
    "@preact/signals": "2.9.0",
    "@preact/signals-core": "1.14.2",
    "preact": "10.29.1",
    "ts-morph": "28.0.0"
  },
  "peerDependencies": {
    "typescript": ">= 5.9.3",
    "elysia": ">= 1.4.0",
    "@elysiajs/eden": ">= 1.2.0",
    "@stryker-mutator/api": ">= 9.0.0"
  },
  "peerDependenciesMeta": {
    "elysia": { "optional": true },
    "@elysiajs/eden": { "optional": true },
    "@stryker-mutator/api": { "optional": true }
  },
  "devDependencies": {
    "@biomejs/biome": "2.4.14",
    "@elysiajs/eden": "1.4.9",
    "@stryker-mutator/api": "9.6.1",
    "@types/bun": "1.3.13",
    "@types/chrome": "0.1.40",
    "elysia": "1.4.28",
    "typescript": "6.0.3"
  },
  "engines": { "bun": ">=1.2.0" },
  "license": "MIT"
}
PKG
ok "package.json written"

# ----------------------------------------------------------------------------
# 7. trimmed build-lib.ts (core browser build + verify/visualize node build)
# ----------------------------------------------------------------------------
log "writing trimmed build-lib.ts …"
cat > "$TARGET/build-lib.ts" <<'BUILD'
#!/usr/bin/env bun
// biome-ignore lint/suspicious/noConsoleLog: Build script needs console output

/**
 * Trimmed build script (generated by vendor-polly.sh).
 *
 * Builds the mesh-free vendored slice:
 *   - core library (browser target)
 *   - polly bin + verify + stryker + visualize CLIs (node target, bundled)
 *   - copies verify's TLA+ specs + Dockerfile
 *   - emits .d.ts declarations
 */

import { existsSync, rmSync, mkdirSync, cpSync } from "node:fs";
import { join } from "node:path";
import { $ } from "bun";

const DIST_DIR = "dist";
if (existsSync(DIST_DIR)) rmSync(DIST_DIR, { recursive: true, force: true });

console.log("🔨 Building library (browser target)...");
const libResult = await Bun.build({
  entrypoints: [
    "src/index.ts",
    "src/shared/lib/state.ts",
    "src/shared/lib/resource.ts",
    "src/shared/lib/message-bus.ts",
    "src/shared/lib/errors.ts",
    "src/shared/lib/guards.ts",
    "src/shared/lib/context-helpers.ts",
    "src/shared/lib/test-helpers.ts",
    "src/shared/adapters/index.ts",
    "src/shared/types/messages.ts",
    "src/shared/state/app-state.ts",
    "src/background/index.ts",
    "src/background/message-router.ts",
    "src/elysia/index.ts",
    "src/client/index.ts",
    "src/actions/index.ts",
    // verify config (the `./verify` subpath export) — browser-safe
    "tools/verify/src/config.ts",
  ],
  outdir: DIST_DIR,
  target: "browser",
  format: "esm",
  splitting: false,
  minify: false,
  sourcemap: "external",
  naming: { entry: "[dir]/[name].[ext]" },
  external: ["preact", "@preact/signals", "@preact/signals-core", "elysia", "@elysiajs/eden", "bun"],
});
if (!libResult.success) {
  console.error("❌ Library build failed:");
  for (const log of libResult.logs) console.error(log);
  process.exit(1);
}
console.log("✅ Library built");

console.log("🔨 Building CLI and tools (node target, bundled)...");
const toolsResult = await Bun.build({
  entrypoints: [
    "cli/polly.ts",
    "tools/verify/src/cli.ts",
    "tools/verify/src/stryker/index.ts",
    "tools/visualize/src/cli.ts",
    // quality library (the `./quality` subpath export) — node-target: it scans
    // source/CSS text via bun's Glob + node:fs, so it is not browser-safe.
    "tools/quality/src/index.ts",
    // quality CLI — the `polly quality` dispatcher (cli/polly.ts) spawns this,
    // so it must be built for `polly quality list/run` to work in the slice.
    "tools/quality/src/cli.ts",
  ],
  outdir: DIST_DIR,
  target: "node",
  format: "esm",
  splitting: false,
  minify: false,
  sourcemap: "external",
  naming: { entry: "[dir]/[name].[ext]" },
  external: ["ts-morph", "bun", "bun:*", "node:*", "elysia", "@elysiajs/*", "@stryker-mutator/*"],
});
if (!toolsResult.success) {
  console.error("❌ Tools build failed:");
  for (const log of toolsResult.logs) console.error(log);
  process.exit(1);
}
console.log("✅ Tools built");

console.log("🔨 Copying verify specs + Dockerfile...");
const specsSrc = join("tools", "verify", "specs");
if (existsSync(specsSrc)) {
  const specsDest = join(DIST_DIR, "tools", "verify", "specs");
  mkdirSync(specsDest, { recursive: true });
  cpSync(specsSrc, specsDest, { recursive: true });
}
const dockerfileSrc = join("tools", "verify", "Dockerfile");
if (existsSync(dockerfileSrc)) {
  await Bun.write(join(DIST_DIR, "tools", "verify", "Dockerfile"), await Bun.file(dockerfileSrc).text());
}
console.log("✅ Specs + Dockerfile copied");

console.log("🔨 Generating TypeScript declarations...");
try {
  const tsconfigPath = "tsconfig.lib.json";
  const tsconfigContent = {
    extends: "./tsconfig.json",
    compilerOptions: {
      declaration: true,
      emitDeclarationOnly: true,
      outDir: "dist",
      rootDir: ".",
      skipLibCheck: true,
      noEmit: false,
    },
    include: [
      "src/**/*",
      "bun-env.d.ts",
      "tools/verify/src/config.ts",
      "tools/verify/src/stryker/index.ts",
      "tools/quality/src/**/*",
    ],
    exclude: ["**/*.test.ts", "**/*.spec.ts"],
  };
  await Bun.write(tsconfigPath, JSON.stringify(tsconfigContent, null, 2));
  await $`bunx tsc --project ${tsconfigPath}`;
  rmSync(tsconfigPath);
  console.log("✅ Declarations generated");
} catch (error) {
  console.error("❌ Failed to generate TypeScript declarations");
  console.error(error);
  process.exit(1);
}

console.log("\n✨ Build complete!");
BUILD
ok "build-lib.ts written"

# ----------------------------------------------------------------------------
# 8. summary + optional verification
# ----------------------------------------------------------------------------
echo
ok "vendored polly into $TARGET"
printf '%s' "$c_dim"
cat <<NOTES
Kept:    core framework, elysia (peerRepo trimmed), verify (+analysis+stryker), visualize, quality
Removed: UI (polly-ui), mesh runtime, chrome-extension contexts, all tests, init/test tooling
Notes:
  - The visualize --snapshot mesh overlay is stubbed (throws if used).
  - 'polly build'/'dev'/'test'/'quality'/'init' subcommands are unavailable
    (their CLIs and scripts/ were not vendored). The quality *library*
    (@fairfox/polly/quality) is exported for programmatic use — wire its
    checks (e.g. checkNoAsCasting, checkNoTautologyEnsures) into your own
    runner, as Polly's scripts/check-*.ts do.
  - @types/chrome is required: the core chrome adapters reference the chrome
    global. @babel/* may be needed if tools/analysis uses it (the build below
    will tell you).
Next:
  cd "$TARGET" && bun install && bun run build:lib
NOTES
printf '%s' "$c_off"

if [ "$CHECK" -eq 1 ]; then
  echo
  log "running --check (bun install + tsc --noEmit) …"
  ( cd "$TARGET" && bun install && bunx tsc --noEmit ) \
    && ok "typecheck passed" \
    || warn "typecheck reported issues — review above (the mesh stub types are the most likely culprit)"
fi
