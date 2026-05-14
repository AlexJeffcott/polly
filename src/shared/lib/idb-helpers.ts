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

export interface OpenIDBOptions {
  name: string;
  version: number;
  /** Invoked inside `onupgradeneeded`. Create object stores here. */
  upgrade: (db: IDBDatabase, event: IDBVersionChangeEvent) => void;
}

/** Open an IndexedDB database with the Polly#107 timeout guard. */
export function openIDB(options: OpenIDBOptions): Promise<IDBDatabase> {
  return new Promise<IDBDatabase>((resolve, reject) => {
    const start = Date.now();
    const request = indexedDB.open(options.name, options.version);
    let settled = false;
    const timer = setTimeout(() => {
      if (settled) return;
      settled = true;
      const elapsedMs = Date.now() - start;
      reject(
        new Error(
          `Polly IndexedDB open of '${options.name}' timed out after ${elapsedMs}ms (cross-tab lock or zombie connection?)`
        )
      );
    }, IDB_OPEN_TIMEOUT_MS);

    request.onerror = () => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      reject(request.error);
    };
    request.onsuccess = () => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve(request.result);
    };
    request.onupgradeneeded = (event) => {
      const db = (event.target as unknown as IDBOpenDBRequest).result;
      options.upgrade(db, event);
    };
  });
}

/** One-shot open caching with retry-on-failure. Caller owns a `{ promise }`
 *  cell; first call opens, subsequent calls return the cached promise, and
 *  a rejected open clears the cache so the next call can retry instead of
 *  being poisoned by one transient failure. */
export function cachedOpen(
  ref: { promise: Promise<IDBDatabase> | null },
  options: OpenIDBOptions
): Promise<IDBDatabase> {
  if (ref.promise) return ref.promise;
  const pending = openIDB(options);
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
      visit(cursor.key, cursor.value as V);
      cursor.continue();
    };
    request.onerror = () => reject(request.error);
  });
}
