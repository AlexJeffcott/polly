/**
 * Tiny internal helpers around the raw IndexedDB API.
 *
 * Wraps the patterns that `storage-adapter.ts` and `blob-cache.ts` both
 * re-implement: timed open with retry-on-failure caching, request→promise
 * wrapping, transaction-to-completion, and cursor iteration. Not exported
 * from the public package — internal to `src/shared/lib`.
 */

/** Polly#107 post-v0.60: hard timeout on `indexedDB.open()`. Healthy
 *  opens land in microseconds; the v0.60.0 fingerprint surfaced a zombie
 *  cross-tab connection that left an open request firing no events at all.
 *  5s is two orders of magnitude beyond the normal upper bound and short
 *  enough that the operator gets a named failure instead of a hung page
 *  when the storage layer wedges. */
export const IDB_OPEN_TIMEOUT_MS = 5000;

export type IDBOpenFailureReason = "timeout" | "blocked" | "error";

/** Structured failure for `openIDB`. `reason` distinguishes the three
 *  recoveries: `timeout` (true zombie, browser restart), `blocked`
 *  (sibling tab holds an older version open — closing it clears the
 *  block immediately), and `error` (unexpected `onerror` from the
 *  request itself). Stays `instanceof Error` for callers that just want
 *  `console.warn(err)`; `instanceof IDBOpenError` + `err.reason` gives
 *  structured handling without regexing the message. */
export class IDBOpenError extends Error {
  readonly reason: IDBOpenFailureReason;
  readonly dbName: string;
  readonly elapsedMs: number;

  constructor(reason: IDBOpenFailureReason, dbName: string, elapsedMs: number, cause?: unknown) {
    super(
      `Polly IndexedDB open of '${dbName}' ${reason} after ${elapsedMs}ms`,
      cause === undefined ? undefined : { cause }
    );
    this.name = "IDBOpenError";
    this.reason = reason;
    this.dbName = dbName;
    this.elapsedMs = elapsedMs;
  }
}

export interface OpenIDBOptions<D = IDBDatabase> {
  name: string;
  version: number;
  /** Invoked inside `onupgradeneeded`. Create object stores here. */
  upgrade: (db: D, event: IDBVersionChangeEvent) => void;
}

/** A handler slot on an open request. Method-typed so the parameter is
 *  bivariant: the DOM slot is `(this: IDBOpenDBRequest, ev: Event) => any`,
 *  a test fake's takes `unknown`. */
type IDBOpenHandler<E> = { handle(event: E): void }["handle"] | null;

/** The part of an `IDBOpenDBRequest` that `openIDB` uses: four handler
 *  slots it writes, and the `result` and `error` it reads. `D` is the
 *  database type the request yields; `IDBOpenDBRequest` satisfies
 *  `IDBOpenRequestLike<IDBDatabase>`. */
export interface IDBOpenRequestLike<D> {
  readonly result: D;
  readonly error: DOMException | null;
  onsuccess: IDBOpenHandler<unknown>;
  onerror: IDBOpenHandler<unknown>;
  onblocked: IDBOpenHandler<unknown>;
  onupgradeneeded: IDBOpenHandler<IDBVersionChangeEvent>;
}

/** Open-request factory. Production passes {@link indexedDBOpen}; tests
 *  pass a fake to force the timeout, blocked, or error path without
 *  needing a real zombie tab — `fake-indexeddb` cannot reproduce the
 *  v0.60.0 no-events fingerprint, so the regression that motivated this
 *  whole module is otherwise uncoverable. */
export type IDBOpenFn<D = IDBDatabase> = (name: string, version: number) => IDBOpenRequestLike<D>;

/** The production factory: `indexedDB.open`, read at call time. */
export const indexedDBOpen: IDBOpenFn = (name, version) => indexedDB.open(name, version);

/** Open an IndexedDB database with the Polly#107 timeout guard. */
export function openIDB<D>(options: OpenIDBOptions<D>, openFn: IDBOpenFn<D>): Promise<D> {
  return new Promise<D>((resolve, reject) => {
    const start = Date.now();
    const request = openFn(options.name, options.version);
    let settled = false;
    const elapsed = () => Date.now() - start;
    const rejectWith = (reason: IDBOpenFailureReason, cause?: unknown) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      reject(new IDBOpenError(reason, options.name, elapsed(), cause));
    };
    const timer = setTimeout(() => rejectWith("timeout"), IDB_OPEN_TIMEOUT_MS);

    request.onerror = () => rejectWith("error", request.error);
    request.onblocked = () => rejectWith("blocked");
    request.onsuccess = () => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve(request.result);
    };
    // During `upgradeneeded` the request's `result` is already the
    // connection (it is the event's target), so read it from the request.
    request.onupgradeneeded = (event) => {
      options.upgrade(request.result, event);
    };
  });
}

/** One-shot open caching with retry-on-failure. Caller owns a `{ promise }`
 *  cell; first call opens, subsequent calls return the cached promise, and
 *  a rejected open clears the cache so the next call can retry instead of
 *  being poisoned by one transient failure. */
export function cachedOpen<D>(
  ref: { promise: Promise<D> | null },
  options: OpenIDBOptions<D>,
  openFn: IDBOpenFn<D>
): Promise<D> {
  if (ref.promise) return ref.promise;
  const pending = openIDB(options, openFn);
  pending.catch(() => {
    if (ref.promise === pending) ref.promise = null;
  });
  ref.promise = pending;
  return pending;
}

/** Promise-wrap a single `IDBRequest` (`get`, `put`, `count`, `delete`…). */
export function runRequest<T>(request: IDBRequest<T>): Promise<T> {
  return new Promise<T>((resolve, reject) => {
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

/** Run a transaction to completion. Resolves on `tx.oncomplete` (write
 *  durability), not on individual request success. Throws inside `fn`
 *  abort the transaction and reject. */
export function runTx(
  db: IDBDatabase,
  storeName: string,
  mode: IDBTransactionMode,
  fn: (store: IDBObjectStore) => void
): Promise<void> {
  return new Promise<void>((resolve, reject) => {
    const tx = db.transaction(storeName, mode);
    const store = tx.objectStore(storeName);
    tx.oncomplete = () => resolve();
    tx.onerror = () => reject(tx.error);
    tx.onabort = () => reject(tx.error);
    try {
      fn(store);
    } catch (err) {
      try {
        tx.abort();
      } catch {
        /* already aborted */
      }
      reject(err);
    }
  });
}

/** Walk every record in a store. */
export function iterateCursor<V>(
  db: IDBDatabase,
  storeName: string,
  visit: (key: IDBValidKey, value: V) => void
): Promise<void> {
  return new Promise<void>((resolve, reject) => {
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const request = store.openCursor();
    request.onsuccess = () => {
      const cursor = request.result;
      if (!cursor) return resolve();
      visit(cursor.key, cursor.value);
      cursor.continue();
    };
    request.onerror = () => reject(request.error);
  });
}
