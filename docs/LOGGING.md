# Logging

Polly funnels every log call into a `LoggerAdapter`. In production
the `MessageLoggerAdapter` forwards entries to a single
`LogStore` running in the background context; in tests the
`createMockLogger` factory captures calls in memory. Application code
never imports `console` directly — it goes through `bus.adapters.logger`.

The store keeps a circular buffer of the last 1,000 entries (configurable)
and answers four message types: `LOG`, `LOGS_GET`, `LOGS_CLEAR`,
`LOGS_EXPORT`.

## Architecture

```
┌─────────────┐        LOG message        ┌────────────────┐
│   Content   │───────────────────────────>│                │
│   Script    │                            │   Background   │
└─────────────┘                            │   LogStore     │
                                           │                │
┌─────────────┐        LOG message        │  - circular    │
│    Popup    │───────────────────────────>│    buffer      │
└─────────────┘                            │  - filtering   │
                                           │  - JSON export │
┌─────────────┐        LOG message        │                │
│   DevTools  │───────────────────────────>│                │
└─────────────┘                            └────────────────┘
                                                    │
                                                    v
                                           ┌────────────────┐
                                           │  LOGS_GET      │
                                           │  LOGS_CLEAR    │
                                           │  LOGS_EXPORT   │
                                           └────────────────┘
```

## The interface

```typescript
// src/shared/adapters/logger.adapter.ts

export type LogLevel = "debug" | "info" | "warn" | "error";

export interface LoggerAdapter {
  debug(message: string, context?: Record<string, unknown>): void;
  info(message: string, context?: Record<string, unknown>): void;
  warn(message: string, context?: Record<string, unknown>): void;
  error(message: string, error?: Error, context?: Record<string, unknown>): void;
  log(level: LogLevel, message: string, context?: Record<string, unknown>): void;
}
```

`context` is an arbitrary structured-metadata bag. Prefer it over
interpolating values into `message`: filtering, searching, and
diffing logs all rely on the fields being separate from the prose.

## Message types

The on-the-wire shapes live in `src/shared/types/messages.ts`:

```typescript
export type LogEntry = {
  id: string;
  level: LogLevel;
  message: string;
  context?: Record<string, unknown>;
  error?: string;
  stack?: string;
  source: Context;
  timestamp: number;
};

// In ExtensionMessage:
| { type: "LOG"; level: LogLevel; message: string; context?: Record<string, unknown>;
    error?: string; stack?: string; source: Context; timestamp: number }
| { type: "LOGS_GET"; filters?: { level?: LogLevel; source?: Context; since?: number; limit?: number } }
| { type: "LOGS_CLEAR" }
| { type: "LOGS_EXPORT" }
```

`source` is the originating context; `LogStore` sets it from the
incoming envelope so it cannot be spoofed by application code.

## Production: `MessageLoggerAdapter`

`MessageLoggerAdapter` (in `src/shared/adapters/logger.adapter.ts`)
fires `LOG` messages directly through the `RuntimeAdapter` rather than
the message bus — using the bus would loop back through its own logger
and produce a cycle. Each call is fire-and-forget; if the runtime
rejects (no receiver yet, service worker reload), the adapter falls
back to `console[level]` when `fallbackToConsole` is true.

The constructor takes the runtime, the local context, and an options
object; the wiring is done for you by `createChromeAdapters`:

```typescript
import { createChromeAdapters } from "@fairfox/polly/adapters";
import { createBackground } from "@fairfox/polly/background";

const adapters = createChromeAdapters("background", { consoleMirror: true });
const bus = createBackground({ adapters });

bus.adapters.logger.info("Service worker ready");
```

`consoleMirror: true` makes the adapter also write to `console` on
each call — useful during local development; off by default.

## Production: `LogStore`

`LogStore` (in `src/background/log-store.ts`) sits inside the
background context and registers handlers for the four `LOGS_*`
message types. Construction is one line; the handlers are wired
automatically:

```typescript
import { LogStore } from "@fairfox/polly/background";

const logStore = new LogStore(bus, { maxLogs: 5000 });
```

If you do not instantiate `LogStore`, `LOG` messages have nowhere to
land and `LOGS_GET`/`LOGS_CLEAR`/`LOGS_EXPORT` will time out. The
production logger still falls back to `console` (see above), so log
output is not lost — but the in-memory buffer and querying surface
require the store.

The buffer is a simple FIFO: the oldest entry is dropped once the
length exceeds `maxLogs` (default 1,000). `LOGS_GET` filters in memory
(level, source, since, limit) and returns the matching entries;
`LOGS_EXPORT` returns the full buffer as JSON; `LOGS_CLEAR` truncates
and returns the dropped count.

## Tests: `createMockLogger`

`createMockLogger` ships from `@fairfox/polly/test`:

```typescript
import { createMockLogger } from "@fairfox/polly/test";

const logger = createMockLogger({ silent: true });
// pass logger into the code under test
expect(logger._calls).toHaveLength(1);
expect(logger._calls[0]?.level).toBe("info");
logger._clear();
```

The returned mock implements `LoggerAdapter` plus two test-only
fields:

```typescript
export interface MockLogger extends LoggerAdapter {
  _calls: LogCall[];
  _clear(): void;
}

export interface LogCall {
  level: LogLevel;
  message: string;
  context?: Record<string, unknown>;
  error?: Error;
  timestamp: number;
}
```

`silent` defaults to `true` so test runs stay quiet. Pass
`silent: false` when debugging a failing test.

`createMockAdapters()` returns a full mock stack with a silent
`createMockLogger()` already installed at `adapters.logger`. See
[TESTING.md](./TESTING.md).

## Querying

The store answers a single filter type with optional fields:

```typescript
const all     = await bus.send({ type: "LOGS_GET" });
const errors  = await bus.send({ type: "LOGS_GET", filters: { level: "error" } });
const content = await bus.send({ type: "LOGS_GET", filters: { source: "content" } });
const recent  = await bus.send({
  type: "LOGS_GET",
  filters: { since: Date.now() - 60_000, limit: 50 },
});
```

Filters compose: `{ level: "error", source: "background", since: t, limit: 10 }`
returns the last ten background error entries after `t`. Filter
ordering does not matter — every filter is applied independently.

## Exporting

```typescript
const { json, count } = await bus.send({ type: "LOGS_EXPORT" });

const blob = new Blob([json], { type: "application/json" });
const url = URL.createObjectURL(blob);
const a = document.createElement("a");
a.href = url;
a.download = `logs-${Date.now()}.json`;
a.click();
URL.revokeObjectURL(url);
```

## Clearing

```typescript
const { count } = await bus.send({ type: "LOGS_CLEAR" });
```

## Choosing a level

- `debug` — verbose, development-only detail. Stripped by the level
  filter in production-facing tooling but still useful in dev builds.
- `info` — events the operator might care about: a service worker
  starting, settings changing, a user logging in.
- `warn` — recoverable conditions that suggest a misconfiguration or
  an unexpected branch. A missing handler, a stale port.
- `error` — exceptional paths. Always pass the `Error` object as the
  second argument so the stack trace makes it into the entry.

```typescript
logger.error("Settings fetch failed", err, { endpoint });
```

## Structured context

Pass values as fields, not as interpolated strings. Filtering and
post-hoc analysis depend on the structure:

```typescript
logger.info("Tab updated", { tabId: tab.id, url: tab.url, status: changeInfo.status });
```

Don't log secrets — passwords, tokens, session cookies, signed
payloads. Treat the log buffer as eventually-public; if it would be a
problem in a support bundle, leave it out.

For high-frequency loops, log a summary rather than each iteration:
one entry with `{ count, durationMs }` is more useful than 10,000
near-identical entries.

## See also

- [ADAPTERS.md](./ADAPTERS.md) — the adapter pattern and how the
  logger sits in `ExtensionAdapters`.
- [ERRORS.md](./ERRORS.md) — `ErrorHandler`, which pairs every error
  with a `logger.error` call.
- [TESTING.md](./TESTING.md) — `createMockAdapters()` and the rest of
  the mock surface.
- [MESSAGING.md](./MESSAGING.md) — how `LOG` and `LOGS_*` flow over
  the bus.
