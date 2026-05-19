# Errors

Polly ships a small family of error classes plus an `ErrorHandler`
that pairs each throw with a log call. The whole surface lives in
`src/shared/lib/errors.ts` and is exported from both the root
(`@fairfox/polly`) and the `/errors` subpath.

```typescript
import {
  ExtensionError,
  TimeoutError,
  ConnectionError,
  MessageRouterError,
  HandlerError,
  APIError,
  OffscreenError,
  ErrorHandler,
} from "@fairfox/polly/errors";
```

## The base class

`ExtensionError` is the root of the hierarchy. Every other class
extends it. It carries a `code` and an optional `context` map:

```typescript
class ExtensionError extends Error {
  readonly code: string;
  readonly context?: Record<string, unknown>;
  constructor(message: string, code: string, context?: Record<string, unknown>);
}
```

The `code` is a stable string (e.g. `"TIMEOUT_ERROR"`). `context` is
an arbitrary metadata bag the throwing site supplies — the most useful
fields to pull out get hoisted into typed properties on the
subclasses (`timeoutMs` on `TimeoutError`, `statusCode` on `APIError`,
etc.).

`name` is set to the constructor name and `Error.captureStackTrace` is
called when supported, so the stack trace points at the throwing
site, not the constructor.

## The classes

| Class | Code | Extra fields | Used by |
|---|---|---|---|
| `TimeoutError` | `TIMEOUT_ERROR` | `timeoutMs: number` | `MessageBus` request/response timeouts (`src/shared/lib/message-bus.ts:170`). |
| `ConnectionError` | `CONNECTION_ERROR` | — | Port disconnects and transport-layer failures (`message-bus.ts:462`). |
| `MessageRouterError` | `MESSAGE_ROUTER_ERROR` | — | `MessageRouter` routing failures, e.g. no content script connected to the target tab (`message-router.ts:319`). |
| `HandlerError` | `HANDLER_ERROR` | `messageType: string` | Failures surfaced from a remote handler back to the caller (`message-bus.ts:549`). |
| `APIError` | `API_ERROR` | `statusCode: number` | HTTP-layer failures from the `fetch` adapter. |
| `OffscreenError` | `OFFSCREEN_ERROR` | — | Failures creating, communicating with, or tearing down an offscreen document. |

`ExtensionError` itself can also be thrown directly when none of the
specialised codes fit; pick a stable `code` string and document it
where the throw lives.

## `ErrorHandler`

`ErrorHandler` is a small helper that pairs each error with a log
call. It is constructed against a `LoggerAdapter` (typically the one
already on the message bus):

```typescript
import { ErrorHandler, TimeoutError } from "@fairfox/polly/errors";

const errorHandler = new ErrorHandler(bus.adapters.logger);

errorHandler.throw(
  new TimeoutError("Settings fetch timed out", 5_000, { context: "settings.load" })
);
```

It exposes three methods:

- `throw(error)` — logs at `error` level, then throws. The return
  type is `never` so TypeScript narrows control flow.
- `reject(error)` — logs at `error` level, then returns the error so
  it can be passed to `Promise.reject` or a `reject(...)` callback.
- `wrap(error, message, code, context?)` — coerces an unknown thrown
  value into an `ExtensionError`. The original `message` is appended,
  the original stack is preserved if present, and `originalError` /
  `originalStack` are copied into `context`. Logs at `error` level
  and returns the wrapped error.

`MessageBus` constructs its own `ErrorHandler` and uses it for every
timeout, port-disconnect, and remote-handler-failure path.
`MessageRouter` and `OffscreenManager` do the same. Application code
is free to instantiate its own against the same logger.

## Throwing and catching

Throws look like any other `Error` throw; catchers use `instanceof`
to pick the family:

```typescript
import { TimeoutError, ConnectionError } from "@fairfox/polly/errors";

try {
  await bus.send({ type: "SETTINGS_GET" });
} catch (err) {
  if (err instanceof TimeoutError) {
    return retry(err.timeoutMs);
  }
  if (err instanceof ConnectionError) {
    return showOfflineBanner();
  }
  throw err;
}
```

When an error crosses the message-bus boundary — a handler throws on
the background side and the response surfaces on the popup side — the
caller receives a `HandlerError` with `messageType` set to the
original request type. The original class is not preserved across the
wire; serialise only what you actually need to act on into
`HandlerError.context`.

## Extending the hierarchy

If your application needs narrower types — for example, a distinct
`StorageError` for storage-adapter failures — define them locally,
extending `ExtensionError`:

```typescript
import { ExtensionError } from "@fairfox/polly/errors";

export class StorageError extends ExtensionError {
  constructor(message: string, context?: Record<string, unknown>) {
    super(message, "STORAGE_ERROR", context);
  }
}
```

The same `code` / `context` contract carries over: `code` is the
identifier `ErrorHandler.wrap` and any consumer code matches on;
`context` is the bag the throwing site fills.
