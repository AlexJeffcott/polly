import { describe, expect, test } from "bun:test";
import {
  cachedOpen,
  IDB_OPEN_TIMEOUT_MS,
  IDBOpenError,
  type IDBOpenFn,
  type OpenIDBOptions,
  openIDB,
} from "../../src/shared/lib/idb-helpers";

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

describe("openIDB", () => {
  test(
    "rejects with IDBOpenError reason='timeout' when the request never fires",
    async () => {
      const { fn } = captureOpenFn();
      const start = Date.now();
      const err = await openIDB(defaultOptions, fn).catch((e) => e);
      const elapsed = Date.now() - start;

      expect(err).toBeInstanceOf(IDBOpenError);
      expect(err).toBeInstanceOf(Error);
      expect((err as IDBOpenError).reason).toBe("timeout");
      expect((err as IDBOpenError).dbName).toBe("polly-test");
      expect((err as IDBOpenError).elapsedMs).toBeGreaterThanOrEqual(IDB_OPEN_TIMEOUT_MS - 50);
      expect(elapsed).toBeGreaterThanOrEqual(IDB_OPEN_TIMEOUT_MS - 50);
      expect(elapsed).toBeLessThan(IDB_OPEN_TIMEOUT_MS + 1000);
    },
    { timeout: IDB_OPEN_TIMEOUT_MS + 2000 }
  );

  test("rejects with reason='blocked' when onblocked fires", async () => {
    const { fn, request } = captureOpenFn();
    const pending = openIDB(defaultOptions, fn);
    queueMicrotask(() => request.onblocked?.({}));

    const err = await pending.catch((e) => e);
    expect(err).toBeInstanceOf(IDBOpenError);
    expect((err as IDBOpenError).reason).toBe("blocked");
    expect((err as IDBOpenError).dbName).toBe("polly-test");
  });

  test("rejects with reason='error' carrying request.error as cause", async () => {
    const { fn, request } = captureOpenFn();
    const underlying = new DOMException("VersionError", "VersionError");
    request.error = underlying;
    const pending = openIDB(defaultOptions, fn);
    queueMicrotask(() => request.onerror?.({}));

    const err = await pending.catch((e) => e);
    expect(err).toBeInstanceOf(IDBOpenError);
    expect((err as IDBOpenError).reason).toBe("error");
    expect((err as IDBOpenError).cause).toBe(underlying);
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
    const ref = { promise: null as Promise<IDBDatabase> | null };

    const first = cachedOpen(ref, defaultOptions, fn);
    const second = cachedOpen(ref, defaultOptions, fn);

    expect(first).toBe(second);
    await first;
    expect(opens).toBe(1);
  });

  test("clears the cache on rejection so the next call retries", async () => {
    const ref = { promise: null as Promise<IDBDatabase> | null };

    const blocked = makeRequest();
    const blockedFn: IDBOpenFn = () => {
      queueMicrotask(() => blocked.onblocked?.({}));
      return blocked as unknown as IDBOpenDBRequest;
    };
    const first = cachedOpen(ref, defaultOptions, blockedFn);
    expect(ref.promise).toBe(first);

    const err = await first.catch((e) => e);
    expect(err).toBeInstanceOf(IDBOpenError);
    expect((err as IDBOpenError).reason).toBe("blocked");
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
