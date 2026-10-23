import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import {
  cachedOpen,
  IDB_OPEN_TIMEOUT_MS,
  IDBOpenError,
  type IDBOpenFn,
  iterateCursor,
  type OpenIDBOptions,
  openIDB,
  runTx,
} from "../../src/shared/lib/idb-helpers";
import { clearGlobals, setGlobal } from "./helpers/globals";

/** Minimal stand-in for `IDBOpenDBRequest`. Only carries the event
 *  handler slots and `result`/`error` fields that `openIDB` touches.
 *  Cast through `unknown` so the helper accepts it via the `openFn`
 *  seam without dragging the full DOM lib type into the fake. */
interface FakeOpenRequest {
  onerror: ((event: unknown) => void) | null;
  onsuccess: ((event: unknown) => void) | null;
  onupgradeneeded: ((event: unknown) => void) | null;
  onblocked: ((event: unknown) => void) | null;
  result: IDBDatabase | null;
  error: DOMException | null;
}

function makeRequest(): FakeOpenRequest {
  return {
    onerror: null,
    onsuccess: null,
    onupgradeneeded: null,
    onblocked: null,
    result: null,
    error: null,
  };
}

const defaultOptions: OpenIDBOptions = {
  name: "polly-test",
  version: 1,
  upgrade: () => {},
};

/** Fake openFn that captures the returned request so the test can
 *  drive its event handlers manually. */
function captureOpenFn(): { fn: IDBOpenFn; request: FakeOpenRequest } {
  const request = makeRequest();
  const fn: IDBOpenFn = () => request as unknown as IDBOpenDBRequest;
  return { fn, request };
}

/** Drop-in fake DB returned by the success path. */
const fakeDB = { close: () => {} } as unknown as IDBDatabase;

/** Narrow a rejection value to IDBOpenError, failing the test otherwise. */
function expectIDBOpenError(err: unknown): IDBOpenError {
  expect(err).toBeInstanceOf(IDBOpenError);
  if (!(err instanceof IDBOpenError)) throw new Error("expected an IDBOpenError rejection");
  return err;
}

describe("openIDB", () => {
  test(
    "rejects with IDBOpenError reason='timeout' when the request never fires",
    async () => {
      const { fn } = captureOpenFn();
      const start = Date.now();
      const err = expectIDBOpenError(await openIDB(defaultOptions, fn).catch((e) => e));
      const elapsed = Date.now() - start;

      expect(err).toBeInstanceOf(Error);
      expect(err.reason).toBe("timeout");
      expect(err.dbName).toBe("polly-test");
      expect(err.elapsedMs).toBeGreaterThanOrEqual(IDB_OPEN_TIMEOUT_MS - 50);
      expect(elapsed).toBeGreaterThanOrEqual(IDB_OPEN_TIMEOUT_MS - 50);
      expect(elapsed).toBeLessThan(IDB_OPEN_TIMEOUT_MS + 1000);
    },
    { timeout: IDB_OPEN_TIMEOUT_MS + 2000 }
  );

  test("rejects with reason='blocked' when onblocked fires", async () => {
    const { fn, request } = captureOpenFn();
    const pending = openIDB(defaultOptions, fn);
    queueMicrotask(() => request.onblocked?.({}));

    const err = expectIDBOpenError(await pending.catch((e) => e));
    expect(err.reason).toBe("blocked");
    expect(err.dbName).toBe("polly-test");
  });

  test("rejects with reason='error' carrying request.error as cause", async () => {
    const { fn, request } = captureOpenFn();
    const underlying = new DOMException("VersionError", "VersionError");
    request.error = underlying;
    const pending = openIDB(defaultOptions, fn);
    queueMicrotask(() => request.onerror?.({}));

    const err = expectIDBOpenError(await pending.catch((e) => e));
    expect(err.reason).toBe("error");
    expect(err.cause).toBe(underlying);
  });

  test("resolves with request.result when onsuccess fires", async () => {
    const { fn, request } = captureOpenFn();
    request.result = fakeDB;
    const pending = openIDB(defaultOptions, fn);
    queueMicrotask(() => request.onsuccess?.({}));

    await expect(pending).resolves.toBe(fakeDB);
  });

  test("ignores duplicate event firings after settle", async () => {
    const { fn, request } = captureOpenFn();
    request.result = fakeDB;
    const pending = openIDB(defaultOptions, fn);
    queueMicrotask(() => {
      request.onsuccess?.({});
      request.onblocked?.({});
      request.onerror?.({});
    });

    await expect(pending).resolves.toBe(fakeDB);
  });
});

describe("cachedOpen", () => {
  test("returns the cached promise on the second call without re-opening", async () => {
    let opens = 0;
    const request = makeRequest();
    request.result = fakeDB;
    const fn: IDBOpenFn = () => {
      opens++;
      queueMicrotask(() => request.onsuccess?.({}));
      return request as unknown as IDBOpenDBRequest;
    };
    const ref: { promise: Promise<IDBDatabase> | null } = { promise: null };

    const first = cachedOpen(ref, defaultOptions, fn);
    const second = cachedOpen(ref, defaultOptions, fn);

    expect(first).toBe(second);
    await first;
    expect(opens).toBe(1);
  });

  test("clears the cache on rejection so the next call retries", async () => {
    const ref: { promise: Promise<IDBDatabase> | null } = { promise: null };

    const blocked = makeRequest();
    const blockedFn: IDBOpenFn = () => {
      queueMicrotask(() => blocked.onblocked?.({}));
      return blocked as unknown as IDBOpenDBRequest;
    };
    const first = cachedOpen(ref, defaultOptions, blockedFn);
    expect(ref.promise).toBe(first);

    const err = expectIDBOpenError(await first.catch((e) => e));
    expect(err.reason).toBe("blocked");
    expect(ref.promise).toBeNull();

    const ok = makeRequest();
    ok.result = fakeDB;
    const okFn: IDBOpenFn = () => {
      queueMicrotask(() => ok.onsuccess?.({}));
      return ok as unknown as IDBOpenDBRequest;
    };
    const second = cachedOpen(ref, defaultOptions, okFn);
    expect(second).not.toBe(first);
    await expect(second).resolves.toBe(fakeDB);
  });
});

// ---------------------------------------------------------------------------
// runTx / iterateCursor — driven against a scriptable in-memory IndexedDB.
//
// The fake is installed on `globalThis.indexedDB` and opened through the
// real `openIDB` default path, so the tests hold a genuinely typed
// `IDBDatabase` without casting the fake. Each transaction is recorded on
// the fake so a test can decide when (and how) it settles.
// ---------------------------------------------------------------------------

class ScriptedRequest<T> {
  onsuccess: (() => void) | null = null;
  onerror: (() => void) | null = null;
  result: T | null = null;
  error: DOMException | null = null;
}

class ScriptedCursor {
  constructor(
    private readonly entries: Array<[IDBValidKey, unknown]>,
    private index: number,
    private readonly request: ScriptedRequest<ScriptedCursor>
  ) {}

  get key(): IDBValidKey | undefined {
    return this.entries[this.index]?.[0];
  }

  get value(): unknown {
    return this.entries[this.index]?.[1];
  }

  continue(): void {
    this.index++;
    const next = this.index < this.entries.length ? this : null;
    setTimeout(() => {
      this.request.result = next;
      this.request.onsuccess?.();
    }, 0);
  }
}

class ScriptedStore {
  constructor(
    private readonly records: Map<IDBValidKey, unknown>,
    private readonly cursorError: DOMException | null
  ) {}

  put(value: unknown, key: IDBValidKey): ScriptedRequest<IDBValidKey> {
    this.records.set(key, value);
    const request = new ScriptedRequest<IDBValidKey>();
    request.result = key;
    return request;
  }

  openCursor(): ScriptedRequest<ScriptedCursor> {
    const request = new ScriptedRequest<ScriptedCursor>();
    const entries = [...this.records.entries()].sort(([a], [b]) =>
      String(a) < String(b) ? -1 : 1
    );
    setTimeout(() => {
      if (this.cursorError) {
        request.error = this.cursorError;
        request.onerror?.();
        return;
      }
      request.result = entries.length > 0 ? new ScriptedCursor(entries, 0, request) : null;
      request.onsuccess?.();
    }, 0);
    return request;
  }
}

class ScriptedTransaction {
  oncomplete: (() => void) | null = null;
  onerror: (() => void) | null = null;
  onabort: (() => void) | null = null;
  error: DOMException | null = null;
  abortCalls = 0;
  /** Real IndexedDB throws InvalidStateError on a second abort. */
  abortThrows = false;

  constructor(
    readonly storeName: string,
    readonly mode: string,
    private readonly store: ScriptedStore
  ) {}

  objectStore(name: string): ScriptedStore {
    if (name !== this.storeName) throw new Error(`store '${name}' not in transaction scope`);
    return this.store;
  }

  abort(): void {
    this.abortCalls++;
    if (this.abortThrows) throw new DOMException("already aborted", "InvalidStateError");
    this.error = null;
    setTimeout(() => this.onabort?.(), 0);
  }

  complete(): void {
    this.oncomplete?.();
  }

  fail(error: DOMException): void {
    this.error = error;
    this.onerror?.();
  }

  abortExternally(error: DOMException): void {
    this.error = error;
    this.onabort?.();
  }
}

class ScriptedDB {
  readonly stores = new Map<string, Map<IDBValidKey, unknown>>();
  readonly transactions: ScriptedTransaction[] = [];
  cursorError: DOMException | null = null;

  createObjectStore(name: string): void {
    this.stores.set(name, new Map());
  }

  transaction(name: string, mode: string): ScriptedTransaction {
    const records = this.stores.get(name);
    if (!records) throw new Error(`store '${name}' was never created`);
    const tx = new ScriptedTransaction(name, mode, new ScriptedStore(records, this.cursorError));
    this.transactions.push(tx);
    return tx;
  }

  lastTx(): ScriptedTransaction {
    const tx = this.transactions.at(-1);
    if (!tx) throw new Error("no transaction was opened");
    return tx;
  }

  close(): void {}
}

interface ScriptedOpenRequest {
  onsuccess: (() => void) | null;
  onerror: (() => void) | null;
  onblocked: (() => void) | null;
  onupgradeneeded: ((event: { target: ScriptedOpenRequest }) => void) | null;
  result: ScriptedDB;
  error: DOMException | null;
}

const STORE = "records";

/** Open a typed `IDBDatabase` over a fresh `ScriptedDB` via the real
 *  `openIDB` default `indexedDB.open` path. */
async function openScripted(): Promise<{ db: IDBDatabase; fake: ScriptedDB }> {
  const fake = new ScriptedDB();
  setGlobal("indexedDB", {
    open: () => {
      const request: ScriptedOpenRequest = {
        onsuccess: null,
        onerror: null,
        onblocked: null,
        onupgradeneeded: null,
        result: fake,
        error: null,
      };
      queueMicrotask(() => {
        request.onupgradeneeded?.({ target: request });
        request.onsuccess?.();
      });
      return request;
    },
  });
  const db = await openIDB({
    name: "polly-tx-test",
    version: 1,
    upgrade: (upgraded) => {
      upgraded.createObjectStore(STORE);
    },
  });
  return { db, fake };
}

/** Settle-state probe: `"pending"` until the promise resolves or rejects. */
function track(promise: Promise<void>): { state: () => string; done: Promise<unknown> } {
  let state = "pending";
  const done = promise.then(
    () => {
      state = "resolved";
    },
    (err: unknown) => {
      state = "rejected";
      return err;
    }
  );
  return { state: () => state, done };
}

const tick = () => new Promise<void>((resolve) => setTimeout(resolve, 0));

describe("runTx", () => {
  let hadIDB = false;
  let savedIDB: unknown;

  beforeEach(() => {
    hadIDB = "indexedDB" in globalThis;
    savedIDB = Reflect.get(globalThis, "indexedDB");
  });

  afterEach(() => {
    if (hadIDB) setGlobal("indexedDB", savedIDB);
    else clearGlobals("indexedDB");
  });

  test("runs fn against the named store in the requested mode", async () => {
    const { db, fake } = await openScripted();
    const pending = runTx(db, STORE, "readwrite", (store) => {
      store.put("one", "k1");
      store.put("two", "k2");
    });
    const tx = fake.lastTx();
    expect(tx.storeName).toBe(STORE);
    expect(tx.mode).toBe("readwrite");
    tx.complete();
    await pending;
    expect([...(fake.stores.get(STORE) ?? new Map()).entries()]).toEqual([
      ["k1", "one"],
      ["k2", "two"],
    ]);
  });

  test("resolves on transaction complete, not before", async () => {
    const { db, fake } = await openScripted();
    const probe = track(runTx(db, STORE, "readwrite", (store) => store.put("v", "k")));
    await tick();
    await tick();
    expect(probe.state()).toBe("pending");
    fake.lastTx().complete();
    await probe.done;
    expect(probe.state()).toBe("resolved");
  });

  test("rejects with tx.error when the transaction errors", async () => {
    const { db, fake } = await openScripted();
    const pending = runTx(db, STORE, "readwrite", () => {});
    const failure = new DOMException("disk full", "QuotaExceededError");
    fake.lastTx().fail(failure);
    expect(await pending.catch((e: unknown) => e)).toBe(failure);
  });

  test("rejects with tx.error when the transaction aborts", async () => {
    const { db, fake } = await openScripted();
    const pending = runTx(db, STORE, "readwrite", () => {});
    const failure = new DOMException("constraint", "ConstraintError");
    fake.lastTx().abortExternally(failure);
    expect(await pending.catch((e: unknown) => e)).toBe(failure);
  });

  test("a throw inside fn aborts the transaction and rejects with the thrown error", async () => {
    const { db, fake } = await openScripted();
    const boom = new Error("callback failed");
    const pending = runTx(db, STORE, "readwrite", () => {
      throw boom;
    });
    expect(await pending.catch((e: unknown) => e)).toBe(boom);
    expect(fake.lastTx().abortCalls).toBe(1);
  });

  test("a throw inside fn still rejects with it when abort itself throws", async () => {
    const { db, fake } = await openScripted();
    const boom = new Error("callback failed after abort");
    const pending = runTx(db, STORE, "readwrite", () => {
      // The callback aborted the transaction itself; the helper's own
      // abort() now throws InvalidStateError and must be swallowed.
      fake.lastTx().abortThrows = true;
      throw boom;
    });
    expect(await pending.catch((e: unknown) => e)).toBe(boom);
    expect(fake.lastTx().abortCalls).toBe(1);
  });
});

describe("iterateCursor", () => {
  let hadIDB = false;
  let savedIDB: unknown;

  beforeEach(() => {
    hadIDB = "indexedDB" in globalThis;
    savedIDB = Reflect.get(globalThis, "indexedDB");
  });

  afterEach(() => {
    if (hadIDB) setGlobal("indexedDB", savedIDB);
    else clearGlobals("indexedDB");
  });

  test("visits every record once, in key order, with key and value", async () => {
    const { db, fake } = await openScripted();
    const records = fake.stores.get(STORE);
    records?.set("b", { n: 2 });
    records?.set("a", { n: 1 });
    records?.set("c", { n: 3 });

    const visited: Array<[IDBValidKey, { n: number }]> = [];
    await iterateCursor<{ n: number }>(db, STORE, (key, value) => visited.push([key, value]));

    expect(visited).toEqual([
      ["a", { n: 1 }],
      ["b", { n: 2 }],
      ["c", { n: 3 }],
    ]);
    expect(fake.lastTx().mode).toBe("readonly");
    expect(fake.lastTx().storeName).toBe(STORE);
  });

  test("resolves only after the last record has been visited", async () => {
    const { db, fake } = await openScripted();
    const records = fake.stores.get(STORE);
    records?.set("a", 1);
    records?.set("b", 2);

    let visits = 0;
    const probe = track(iterateCursor<number>(db, STORE, () => visits++));
    await tick();
    expect(visits).toBe(1);
    expect(probe.state()).toBe("pending");
    await probe.done;
    expect(visits).toBe(2);
    expect(probe.state()).toBe("resolved");
  });

  test("resolves without visiting when the store is empty", async () => {
    const { db } = await openScripted();
    let visits = 0;
    await iterateCursor(db, STORE, () => visits++);
    expect(visits).toBe(0);
  });

  test("rejects with request.error when the cursor request fails", async () => {
    const { db, fake } = await openScripted();
    const failure = new DOMException("cursor broke", "UnknownError");
    fake.cursorError = failure;
    let visits = 0;
    const result = await iterateCursor(db, STORE, () => visits++).catch((e: unknown) => e);
    expect(result).toBe(failure);
    expect(visits).toBe(0);
  });
});
