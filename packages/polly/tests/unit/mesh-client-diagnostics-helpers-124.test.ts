/**
 * Unit tests for mesh-client's already-pure diagnostics helpers (polly#124),
 * pinned directly through the __test__ seam rather than the integration-only
 * factory:
 *
 *   - findLazyWrapperDocIdDuplicates — the polly#107 wrapper/handle off-by-one
 *     detector (group by docId, emit where count > 1)
 *   - getReevaluateDocumentShare — the tolerant lift of the @hidden
 *     synchronizer method, bound to the synchronizer
 *   - installPolly107SyncReevaluation — the env-gated peer-candidate hook
 *
 * Hand-built stubs only.
 */
import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import type { Repo } from "@automerge/automerge-repo/slim";
import { __test__ } from "@/shared/lib/mesh-client";
import type { MeshNetworkAdapter } from "@/shared/lib/mesh-network-adapter";

const {
  findLazyWrapperDocIdDuplicates,
  getReevaluateDocumentShare,
  installPolly107SyncReevaluation,
} = __test__;

type Any = ReturnType<typeof JSON.parse>;

const records = (pairs: Array<[key: string, docId: string]>): Any =>
  pairs.map(([key, docId]) => ({ key, docId })) as Any;

describe("findLazyWrapperDocIdDuplicates — count > 1 threshold (#124)", () => {
  test("a docId appearing once is NOT a duplicate (kills > → >=)", () => {
    expect(findLazyWrapperDocIdDuplicates(records([["k1", "docA"]]))).toEqual([]);
  });

  test("a docId appearing twice IS a duplicate with recordCount 2", () => {
    const dupes = findLazyWrapperDocIdDuplicates(
      records([
        ["k1", "docA"],
        ["k1", "docA"],
      ])
    );
    expect(dupes).toEqual([{ docId: "docA", keys: ["k1"], recordCount: 2 }]);
  });

  test("two distinct keys hashing to one docId report both keys", () => {
    const dupes = findLazyWrapperDocIdDuplicates(
      records([
        ["k1", "docA"],
        ["k2", "docA"],
      ])
    );
    expect(dupes).toHaveLength(1);
    expect(dupes[0]?.docId).toBe("docA");
    expect([...(dupes[0]?.keys ?? [])].sort()).toEqual(["k1", "k2"]);
    expect(dupes[0]?.recordCount).toBe(2);
  });

  test("three records on one docId report recordCount 3 (kills count constant mutants)", () => {
    const dupes = findLazyWrapperDocIdDuplicates(
      records([
        ["k1", "docA"],
        ["k1", "docA"],
        ["k1", "docA"],
      ])
    );
    expect(dupes[0]?.recordCount).toBe(3);
  });

  test("empty input returns an empty array", () => {
    expect(findLazyWrapperDocIdDuplicates(records([]))).toEqual([]);
  });
});

describe("getReevaluateDocumentShare — typeof-function guard (#124)", () => {
  test("returns undefined when the synchronizer is absent", () => {
    expect(getReevaluateDocumentShare({} as unknown as Repo)).toBeUndefined();
  });

  test("returns undefined when reevaluateDocumentShare is not a function", () => {
    const repo = { synchronizer: { reevaluateDocumentShare: 123 } } as unknown as Repo;
    expect(getReevaluateDocumentShare(repo)).toBeUndefined();
  });

  test("returns a caller bound to the synchronizer (kills fn.call(sync) → fn())", async () => {
    let boundThis: unknown;
    const synchronizer = {
      reevaluateDocumentShare(this: unknown): Promise<void> {
        boundThis = this;
        return Promise.resolve();
      },
    };
    const fn = getReevaluateDocumentShare({ synchronizer } as unknown as Repo);
    expect(fn).toBeDefined();
    await fn?.();
    expect(boundThis).toBe(synchronizer);
  });
});

describe("installPolly107SyncReevaluation — env gate + wiring (#124)", () => {
  let saved: string | undefined;
  beforeEach(() => {
    saved = process.env["POLLY_107_DISABLE_FIX"];
    Reflect.deleteProperty(process.env, "POLLY_107_DISABLE_FIX");
  });
  afterEach(() => {
    if (saved === undefined) Reflect.deleteProperty(process.env, "POLLY_107_DISABLE_FIX");
    else process.env["POLLY_107_DISABLE_FIX"] = saved;
  });

  function fakeAdapter(): { adapter: MeshNetworkAdapter; emit: () => void; onCalls: number } {
    let handler: (() => void) | undefined;
    const state = { onCalls: 0 };
    const adapter = {
      on(event: string, cb: () => void): void {
        state.onCalls += 1;
        if (event === "peer-candidate") handler = cb;
      },
    } as unknown as MeshNetworkAdapter;
    return {
      adapter,
      emit: () => handler?.(),
      get onCalls() {
        return state.onCalls;
      },
    } as Any;
  }

  function repoWithReevaluate(spy: () => Promise<void>): Repo {
    return { synchronizer: { reevaluateDocumentShare: spy } } as unknown as Repo;
  }

  test("wires peer-candidate so emitting invokes reevaluate", async () => {
    let calls = 0;
    const spy = (): Promise<void> => {
      calls += 1;
      return Promise.resolve();
    };
    const fake = fakeAdapter();
    installPolly107SyncReevaluation(fake.adapter, repoWithReevaluate(spy));
    fake.emit();
    await Promise.resolve();
    expect(calls).toBe(1);
  });

  test("POLLY_107_DISABLE_FIX=1 short-circuits before wiring", () => {
    process.env["POLLY_107_DISABLE_FIX"] = "1";
    const fake = fakeAdapter();
    installPolly107SyncReevaluation(
      fake.adapter,
      repoWithReevaluate(() => Promise.resolve())
    );
    expect(fake.onCalls).toBe(0);
  });

  test("an env value other than '1' does NOT disable the fix", () => {
    process.env["POLLY_107_DISABLE_FIX"] = "0";
    const fake = fakeAdapter();
    installPolly107SyncReevaluation(
      fake.adapter,
      repoWithReevaluate(() => Promise.resolve())
    );
    expect(fake.onCalls).toBe(1);
  });

  test("a missing reevaluate method short-circuits without wiring", () => {
    const fake = fakeAdapter();
    installPolly107SyncReevaluation(fake.adapter, {} as unknown as Repo);
    expect(fake.onCalls).toBe(0);
  });

  test("the wired handler swallows a rejected reevaluate without throwing", async () => {
    const fake = fakeAdapter();
    installPolly107SyncReevaluation(
      fake.adapter,
      repoWithReevaluate(() => Promise.reject(new Error("boom")))
    );
    expect(() => fake.emit()).not.toThrow();
    await Promise.resolve();
  });
});
