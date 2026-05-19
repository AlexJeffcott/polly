# Adapters

Polly does not call `chrome.*`, `globalThis.fetch`, or `console.log`
directly. Every browser- or platform-specific API it touches goes
through a typed adapter, and the application supplies the adapter
stack at construction time. The pattern keeps the framework testable,
keeps a single bus implementation working across Chrome extensions
and PWAs, and gives applications a single seam to swap behaviour
(decorate, mock, rewire) without forking framework code.

This document describes the **bus-side adapter stack** — the eight
APIs that `MessageBus` and `MessageRouter` need. State primitives use
a separate, smaller stack (`storage` + `sync`); see [STATE.md](./STATE.md)
for that.

## The eight adapters

All eight interfaces live in `src/shared/adapters/`. `ExtensionAdapters`
in `src/shared/adapters/index.ts` is the aggregate shape:

```typescript
export interface ExtensionAdapters {
  runtime: RuntimeAdapter;
  storage: StorageAdapter;
  tabs: TabsAdapter;
  window: WindowAdapter;
  offscreen: OffscreenAdapter;
  contextMenus: ContextMenusAdapter;
  fetch: FetchAdapter;
  logger: LoggerAdapter;
}
```

| Adapter | File | Wraps | Used for |
|---|---|---|---|
| `RuntimeAdapter` | `runtime.adapter.ts` | `chrome.runtime` | `sendMessage`, `onMessage`, `connect`/`Port`, `getURL`, `getId`, `openOptionsPage`. The message bus's transport. |
| `StorageAdapter` | `storage.adapter.ts` | `chrome.storage` | `get`/`set`/`remove`, change events. The persistent backing store for `$sharedState` and `$persistedState`. |
| `TabsAdapter` | `tabs.adapter.ts` | `chrome.tabs` | Query, get current, send to tab, reload, focus. |
| `WindowAdapter` | `window.adapter.ts` | `chrome.windows` | Create / get / focus window. |
| `OffscreenAdapter` | `offscreen.adapter.ts` | `chrome.offscreen` | Create / close offscreen documents for clipboard, audio, DOM-parsing work. |
| `ContextMenusAdapter` | `context-menus.adapter.ts` | `chrome.contextMenus` | Create, remove, listen for clicks. |
| `FetchAdapter` | `fetch.adapter.ts` | `fetch` | HTTP requests; substitutable for tests and Node. |
| `LoggerAdapter` | `logger.adapter.ts` | `console` + log store | Structured logging that flows through the message bus to the popup-side log store. |

The interfaces themselves are short — each file is the authoritative
description, and re-listing them here would drift. The fields are not
hidden behind `any`: callbacks take typed `MessageSender`,
`PortAdapter`, and so on. Open the file in your editor when you need
the signature; the JSDoc on each method is the contract.

## Concrete implementations

| Flavour | Where | Used by |
|---|---|---|
| Chrome | `src/shared/adapters/chrome/*.chrome.ts` | Production Chrome extensions. |
| Browser | `BrowserFetchAdapter` in `fetch.adapter.ts`, `MessageLoggerAdapter` in `logger.adapter.ts` | Shared across Chrome and web apps where the implementation is platform-agnostic. |
| Web | `src/shared/lib/storage-adapter.ts` (`IndexedDBAdapter`, `MemoryStorageAdapter`), `src/shared/lib/sync-adapter.ts` (`BroadcastChannelSyncAdapter`) | PWAs and worker-based apps that need the state primitives but no `chrome.*`. |
| Mock | `tools/test/src/adapters/*.mock.ts` | Tests. Every adapter has a `createMock*` factory; see [TESTING.md](./TESTING.md). |

## Wiring them up

Use the factory that matches your runtime:

```typescript
import { createChromeAdapters } from "@fairfox/polly/adapters";
import { createBackground } from "@fairfox/polly/background";

const adapters = createChromeAdapters("background", { consoleMirror: true });
const bus = createBackground({ adapters });
```

The factory signatures, all in `src/shared/adapters/index.ts` and
`src/shared/lib/adapter-factory.ts`:

- `createChromeAdapters(context, options?): ExtensionAdapters` — the
  full eight-adapter Chrome stack. `consoleMirror: true` makes the
  `MessageLoggerAdapter` also write to `console` for local debugging.
- `createWebAdapters(options?)` — IndexedDB + BroadcastChannel sync
  for PWAs.
- `createNodeAdapters()` — in-memory storage + no-op sync for Node /
  Bun processes.
- `createMockAdapters()` — every adapter is a mock that records its
  calls and exposes seeding helpers; see [TESTING.md](./TESTING.md).
- `createStateAdapters(options?)` — auto-detects the runtime and
  returns just the `{ storage, sync }` pair the state primitives need.

All of these are also exported from `@fairfox/polly/adapters`. A
consumer that needs to override one adapter (say, swap `FetchAdapter`
for a test double in production while keeping the others) builds the
stack manually:

```typescript
import {
  ChromeRuntimeAdapter,
  ChromeStorageAdapter,
  ChromeTabsAdapter,
  ChromeWindowAdapter,
  ChromeOffscreenAdapter,
  ChromeContextMenusAdapter,
  MessageLoggerAdapter,
  type FetchAdapter,
  type ExtensionAdapters,
} from "@fairfox/polly/adapters";

function buildAdapters(context: Context, fetch: FetchAdapter): ExtensionAdapters {
  const runtime = new ChromeRuntimeAdapter();
  return {
    runtime,
    storage: new ChromeStorageAdapter(),
    tabs: new ChromeTabsAdapter(),
    window: new ChromeWindowAdapter(),
    offscreen: new ChromeOffscreenAdapter(),
    contextMenus: new ChromeContextMenusAdapter(),
    fetch,
    logger: new MessageLoggerAdapter(runtime, context, { fallbackToConsole: true }),
  };
}
```

## Dependency injection at the call sites

The bus, the router, and the higher-level helpers all accept adapters
as a constructor argument:

```typescript
// Background script
import { createBackground } from "@fairfox/polly/background";
const bus = createBackground({ adapters: createChromeAdapters("background") });

// Any context
import { createContext } from "@fairfox/polly";
const bus = createContext("popup", { adapters: createChromeAdapters("popup") });

// Low-level
import { MessageBus } from "@fairfox/polly/message-bus";
const bus = new MessageBus("content", createChromeAdapters("content"));
```

In tests, swap the call for `createMockAdapters()`:

```typescript
import { createMockAdapters } from "@fairfox/polly/test";
const bus = new MessageBus("popup", createMockAdapters());
```

The single seam means tests, decorators, and per-deployment overrides
all share one mechanism. There is no global adapter registry.

## Extending an adapter

The simplest extension is to subclass or wrap. For example, a logger
decorator that adds a `traceId` to every entry:

```typescript
import {
  MessageLoggerAdapter,
  type LoggerAdapter,
} from "@fairfox/polly/adapters";

class TracingLogger implements LoggerAdapter {
  constructor(private inner: LoggerAdapter, private traceId: string) {}
  info(msg, ctx)  { this.inner.info(msg, { ...ctx, traceId: this.traceId }); }
  warn(msg, ctx)  { this.inner.warn(msg, { ...ctx, traceId: this.traceId }); }
  error(msg, err, ctx) { this.inner.error(msg, err, { ...ctx, traceId: this.traceId }); }
  debug(msg, ctx) { this.inner.debug(msg, { ...ctx, traceId: this.traceId }); }
}

const adapters = createChromeAdapters("background");
adapters.logger = new TracingLogger(adapters.logger, crypto.randomUUID());
```

The same pattern works for any adapter the framework consumes — the
type is the contract; the implementation is the consumer's choice.

## See also

- [LOGGING.md](./LOGGING.md) — `LoggerAdapter` in depth, including the
  log store and the `LOG`/`LOGS_GET`/`LOGS_CLEAR`/`LOGS_EXPORT`
  message types.
- [TESTING.md](./TESTING.md) — the mock-adapter surface and how to
  build tests against `createMockAdapters()`.
- [STATE.md](./STATE.md) — the storage/sync adapter pair used by the
  state primitives, separate from the bus stack documented here.
