# Documentation

Reference docs for `@fairfox/polly`. The entry-point pitch and the
smallest end-to-end example live in the [root README](../README.md);
this directory is the per-feature reference.

## Core

| Doc | Covers |
|-----|--------|
| [STATE.md](./STATE.md) | The four reactive state primitives (`$state`, `$persistedState`, `$syncedState`, `$sharedState`), `$resource`, the peer/mesh tiers (`$peerState`, `$meshState` and their text/counter/list variants), and the decision tree for picking one. |
| [MESSAGING.md](./MESSAGING.md) | The `MessageBus`/`MessageRouter` cross-context messaging system, routing envelopes, request/response shapes, and the typed-message protocol. |
| [ADAPTERS.md](./ADAPTERS.md) | The adapter pattern over browser/platform APIs (`runtime`, `storage`, `tabs`, `window`, `offscreen`, `contextMenus`, `fetch`, `logger`), plus the Chrome, web, Node, and mock implementations. |
| [BACKGROUND_SETUP.md](./BACKGROUND_SETUP.md) | `createBackground()` vs `getMessageBus()`, the `MessageRouter` singleton, and the double-execution guard. |
| [ACTIONS.md](./ACTIONS.md) | The action-registry pattern, event delegation, store providers, and `runAction` for testing. |
| [UI.md](./UI.md) | The polly-ui component library — `Layout`, `Modal`, `ActionForm`, `Toast`, dialogs, and the three stylesheets (`styles.css`, `theme.css`, `components.css`). |
| [CSS.md](./CSS.md) | The token-driven styling contract polly-ui enforces, and the four CSS conformance checks (`css-quality`, `css-layout`, `css-vars`, `css-unused`). |
| [LOGGING.md](./LOGGING.md) | The logger adapter — `LogStore`, `LogLevel`, `LogEntry`, the `MessageLoggerAdapter` bridge, and querying/exporting from the popup. |
| [ERRORS.md](./ERRORS.md) | The error types in `src/shared/lib/errors.ts` (`ExtensionError`, `TimeoutError`, `ConnectionError`, `MessageRouterError`, `HandlerError`, `APIError`, `OffscreenError`) and `ErrorHandler`. |
| [TESTING.md](./TESTING.md) | Mock adapters, the browser harness (`@fairfox/polly/test/browser`), `runAction`/`createMockStores` for action tests, and the visual-baseline harness. |

## Verification

| Doc | Covers |
|-----|--------|
| [TLA_RESOURCES.md](./TLA_RESOURCES.md) | TLA+ tutorials, references, and troubleshooting notes — useful background for `polly verify`. |
| [RFC-041-peer-first.md](./RFC-041-peer-first.md) | Design of the peer-first state tier (`$peerState`). |
| [RFC-041-peer-first-webrtc.md](./RFC-041-peer-first-webrtc.md) | The WebRTC transport for the mesh tier (`$meshState`). |
| [RFC-041-choosing.md](./RFC-041-choosing.md) | Decision tree across the three resilience tiers (`$sharedState`, `$peerState`, `$meshState`). |
| [RFC-042-blob-sync.md](./RFC-042-blob-sync.md) | The content-addressed blob store that rides on the mesh transport. |

## Generated

- [architecture.dsl](./architecture.dsl) — Structurizr DSL produced by `polly visualize`.

## Quick links

- New to the project? Start with the [root README](../README.md).
- Picking a state primitive? [STATE.md](./STATE.md) has the decision tree.
- Writing tests? [TESTING.md](./TESTING.md).
- Wiring an adapter? [ADAPTERS.md](./ADAPTERS.md).
- Running formal verification? [TLA_RESOURCES.md](./TLA_RESOURCES.md) and the `verify` config in `examples/todo-list/`.
