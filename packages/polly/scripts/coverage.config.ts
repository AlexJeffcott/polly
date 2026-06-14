/**
 * Per-file coverage policy. Read by `scripts/enforce-coverage.ts`.
 *
 * The point of this file is to make polly's tiered test strategy *legible and
 * enforced*: a source file may sit below the unit-coverage floor only if it is
 * genuinely exercised at a higher tier (browser, e2e-mesh, the unpacked
 * extension) — and the exemption must name the test that makes that true.
 * This is the missing link between the tiers. `bun test --coverage` proves a
 * unit number; nothing else proves "this unit-thin file IS covered, and here
 * is the script that covers it." That gap is exactly how a feature stays green
 * across three tiers while never being wired to the entry point the user
 * touches (polly#57 / fairfox#6).
 *
 *   - `defaultThreshold`: applied to every covered file not listed in `exempt`.
 *     Both `lines` and `funcs` must meet or exceed it.
 *   - `exempt`: files NOT subject to the floor. Each entry carries `reason`
 *     (why it is thin at the unit tier) and `claimedBy` (the test/script that
 *     exercises it higher up). The enforcer fails if either path is missing on
 *     disk, so a dead exemption can't silently rot, and it fails if an exempt
 *     file has since climbed past the floor, so the list stays honest.
 *
 * The shape is TS (not JSON) on purpose: the comments document the tiering
 * decision next to the decision itself.
 *
 * The floor is 80/80. It started at 70/40 as a deliberate starting line; the
 * band files were then driven up with real tests (state.ts via the rescued
 * src/__tests__ suites, message-bus.ts routers, actions/testing.ts, TextInput)
 * or exempted where their uncovered code is genuinely higher-tier (mesh-state,
 * message-router — see below).
 */

// The policy types now live with the reusable engine that `polly coverage`
// ships to consumers; Polly dogfoods that same engine against this config.
import type { CoverageConfig } from "../tools/test/src/coverage-policy/types";

export const config: CoverageConfig = {
  defaultThreshold: { lines: 80, funcs: 80 },
  // Polly runs its unit suite from the `tests/` workspace, so the coverage
  // table reports source as `../src/...`; the engine normalises that.
  testCwd: "tests",
  exempt: {
    // ── Runtime-heavy modules whose uncovered code is genuinely exercised at
    //    a higher tier, not at the unit tier. ──
    "src/shared/lib/mesh-state.ts": {
      reason:
        "$meshState/$meshText/$meshCounter/$meshList — the pure wrappers are unit-tested; the Automerge replica + WebRTC sync paths only run with real peers",
      claimedBy: "scripts/e2e-mesh-three-peer-convergence.ts",
    },
    "src/background/message-router.ts": {
      reason:
        "routing logic is unit-tested; the uncovered functions are chrome.runtime/tabs port wiring (onConnect/onMessage/onDisconnect, tab listeners) that only fire inside the MV3 background",
      claimedBy: "scripts/e2e-extension-storage.ts",
    },

    // ── Chrome API adapters: thin shims over `chrome.*` that only execute
    //    inside the unpacked extension. Not reachable from happy-dom. ──
    "src/shared/adapters/chrome/storage.chrome.ts": {
      reason: "chrome.storage shim; the real read/write path runs in the extension",
      claimedBy: "scripts/e2e-extension-storage.ts",
    },
    "src/shared/adapters/chrome/runtime.chrome.ts": {
      reason: "chrome.runtime messaging shim; only live inside the extension",
      claimedBy:
        "n/a — extension-only Chrome API shim, exercised when the unpacked extension loads",
    },
    "src/shared/adapters/chrome/tabs.chrome.ts": {
      reason: "chrome.tabs shim; only live inside the extension",
      claimedBy:
        "n/a — extension-only Chrome API shim, exercised when the unpacked extension loads",
    },
    "src/shared/adapters/chrome/context-menus.chrome.ts": {
      reason: "chrome.contextMenus shim; only live inside the extension",
      claimedBy:
        "n/a — extension-only Chrome API shim, exercised when the unpacked extension loads",
    },
    "src/shared/adapters/chrome/offscreen.chrome.ts": {
      reason: "chrome.offscreen document shim; only live inside the extension",
      claimedBy:
        "n/a — extension-only Chrome API shim, exercised when the unpacked extension loads",
    },
    "src/shared/adapters/chrome/window.chrome.ts": {
      reason: "chrome.windows shim; only live inside the extension",
      claimedBy:
        "n/a — extension-only Chrome API shim, exercised when the unpacked extension loads",
    },

    // ── Adapter wiring + facades: env-driven barrels and logging/fetch
    //    facades that are pure glue at the unit tier. ──
    "src/shared/adapters/index.ts": {
      reason: "adapter barrel/factory; selects the chrome- vs web-target impl by environment",
      claimedBy: "n/a — composition glue; the selected impls are unit- or e2e-covered individually",
    },
    "src/shared/adapters/logger.adapter.ts": {
      reason: "console logging facade; the branches differ only by environment",
      claimedBy: "n/a — console facade, exercised by every extension/e2e invocation",
    },
    "src/shared/adapters/fetch.adapter.ts": {
      reason: "fetch facade; the network path is environment-specific",
      claimedBy: "n/a — fetch facade, exercised by the relay/mesh e2e tiers over real sockets",
    },

    // ── Background-script wiring: registers listeners against chrome.* at
    //    extension start; the handlers it wires are unit-tested separately. ──
    "src/background/context-menu.ts": {
      reason: "registers the context-menu against chrome.contextMenus at extension boot",
      claimedBy: "n/a — background wiring; the menu handlers are unit-tested in isolation",
    },

    // ── Browser-tier / JSX-bound modules kept out of the happy-dom unit run
    //    by the JSX cwd gotcha (see the polly-ui coverage memory). ──
    "src/actions/store.tsx": {
      reason:
        "root store + action dispatchers; the JSX cwd gotcha keeps it out of the unit mutation matrix",
      claimedBy:
        "n/a — no browser test mounts the root store yet; dispatchers run when the full app mounts. A tests/browser store-mount test would let this claim a real file",
    },
    "src/actions/event-delegation.ts": {
      reason:
        "data-action DOM event wiring; only meaningful against a live DOM in the browser tier",
      claimedBy: "tests/browser/actions/event-delegation.browser.ts",
    },
    "src/polly-ui/Dropdown.tsx": {
      reason:
        "Dropdown.positionMenu is browser-only menu geometry (~33% structural ceiling); the rest is in the polly-ui unit matrix",
      claimedBy:
        "n/a — positionMenu needs real layout; covered manually + by the polly-ui browser primitives",
    },

    // ── Blob cache: the LRU/eviction internals are unit-tested; the
    //    request/transfer round-trip is a mesh e2e. ──
    "src/shared/lib/blob-cache.ts": {
      reason:
        "cache internals unit-tested; the request → transfer → cache round-trip is a mesh e2e",
      claimedBy: "scripts/e2e-mesh-blob-transfer.ts",
    },

    // ── Client/server guard: a single throw-if-server module. ──
    "src/shared/lib/_client-only.ts": {
      reason: "client-only guard; the server branch throws and is asserted once",
      claimedBy:
        "n/a — single-branch guard; the throw path is asserted in unit tests, the no-op path is every browser test",
    },
  },
};
