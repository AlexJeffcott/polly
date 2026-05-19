import { afterEach, describe, expect, test } from "bun:test";
import { type DocHandle, Repo } from "@automerge/automerge-repo";
import {
  $crdtCounter,
  $crdtList,
  $crdtText,
  type CounterDoc,
  type ListDoc,
  type TextDoc,
} from "@/shared/lib/crdt-specialised";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";

function makeRepo(): Repo {
  return new Repo();
}

afterEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

describe("$crdtText", () => {
  test("exposes the initial string value synchronously", () => {
    const repo = makeRepo();
    const text = $crdtText("text-1", "hello", {
      getHandle: async () => repo.create<TextDoc>({}),
    });
    expect(text.value).toBe("hello");
    expect(text.key).toBe("text-1");
    expect(text.primitive).toBe("peerState");
  });

  test("loads and exposes the document text after hydration", async () => {
    const repo = makeRepo();
    const text = $crdtText("text-2", "", {
      getHandle: async () => repo.create<TextDoc>({ text: "from-doc" }),
    });
    await text.loaded;
    expect(text.value).toBe("from-doc");
  });

  test("writing to value updates the underlying document text", async () => {
    const repo = makeRepo();
    const text = $crdtText("text-3", "", {
      getHandle: async () => repo.create<TextDoc>({}),
    });
    await text.loaded;
    text.value = "first write";
    await Promise.resolve();
    expect((text.handle as unknown as DocHandle<TextDoc>).doc().text).toBe("first write");
  });

  test("subsequent writes preserve text via updateText splices", async () => {
    const repo = makeRepo();
    const text = $crdtText("text-4", "", {
      getHandle: async () => repo.create<TextDoc>({}),
    });
    await text.loaded;
    text.value = "abc";
    await Promise.resolve();
    text.value = "abcdef";
    await Promise.resolve();
    text.value = "axdef";
    await Promise.resolve();
    expect((text.handle as unknown as DocHandle<TextDoc>).doc().text).toBe("axdef");
  });

  test("remote changes propagate back to the signal", async () => {
    const repo = makeRepo();
    const text = $crdtText("text-5", "", {
      getHandle: async () => repo.create<TextDoc>({ text: "initial" }),
    });
    await text.loaded;
    (text.handle as unknown as DocHandle<TextDoc>).change((doc) => {
      doc.text = "from-remote";
    });
    await Promise.resolve();
    expect(text.value).toBe("from-remote");
  });
});

describe("$crdtCounter", () => {
  test("exposes the initial number value synchronously", () => {
    const repo = makeRepo();
    const counter = $crdtCounter("counter-1", 0, {
      getHandle: async () => repo.create<CounterDoc>({}),
    });
    expect(counter.value).toBe(0);
  });

  test("writing to value initialises the underlying Counter", async () => {
    const repo = makeRepo();
    const counter = $crdtCounter("counter-2", 0, {
      getHandle: async () => repo.create<CounterDoc>({}),
    });
    await counter.loaded;
    counter.value = 5;
    await Promise.resolve();
    const doc = (counter.handle as unknown as DocHandle<CounterDoc>).doc();
    expect(doc.count?.value).toBe(5);
  });

  test("subsequent writes record increments not replacements", async () => {
    const repo = makeRepo();
    const counter = $crdtCounter("counter-3", 0, {
      getHandle: async () => repo.create<CounterDoc>({}),
    });
    await counter.loaded;
    counter.value = 5;
    await Promise.resolve();
    counter.value = 7;
    await Promise.resolve();
    counter.value = 3;
    await Promise.resolve();
    const doc = (counter.handle as unknown as DocHandle<CounterDoc>).doc();
    expect(doc.count?.value).toBe(3);
  });

  test("the read-then-write idiom captures increments correctly", async () => {
    const repo = makeRepo();
    const counter = $crdtCounter("counter-4", 0, {
      getHandle: async () => repo.create<CounterDoc>({}),
    });
    await counter.loaded;
    counter.value += 1;
    await Promise.resolve();
    counter.value += 1;
    await Promise.resolve();
    counter.value += 1;
    await Promise.resolve();
    expect(counter.value).toBe(3);
    const doc = (counter.handle as unknown as DocHandle<CounterDoc>).doc();
    expect(doc.count?.value).toBe(3);
  });

  test("remote increments propagate back to the signal", async () => {
    const repo = makeRepo();
    const counter = $crdtCounter("counter-5", 0, {
      getHandle: async () => repo.create<CounterDoc>({}),
    });
    await counter.loaded;
    counter.value = 10;
    await Promise.resolve();

    (counter.handle as unknown as DocHandle<CounterDoc>).change((doc) => {
      doc.count?.increment(5);
    });
    await Promise.resolve();
    expect(counter.value).toBe(15);
  });
});

describe("$crdtList", () => {
  test("exposes the initial array value synchronously", () => {
    const repo = makeRepo();
    const todos = $crdtList<string>("list-1", ["a"], {
      getHandle: async () => repo.create<ListDoc<string>>({}),
    });
    expect(todos.value).toEqual(["a"]);
  });

  test("writing to value updates the underlying items field", async () => {
    const repo = makeRepo();
    const todos = $crdtList<number>("list-2", [], {
      getHandle: async () => repo.create<ListDoc<number>>({}),
    });
    await todos.loaded;
    todos.value = [1, 2, 3];
    await Promise.resolve();
    const doc = (todos.handle as unknown as DocHandle<ListDoc<number>>).doc();
    expect([...(doc.items ?? [])]).toEqual([1, 2, 3]);
  });

  test("appends survive sequential writes", async () => {
    const repo = makeRepo();
    const todos = $crdtList<string>("list-3", [], {
      getHandle: async () => repo.create<ListDoc<string>>({}),
    });
    await todos.loaded;
    todos.value = ["a"];
    await Promise.resolve();
    todos.value = ["a", "b"];
    await Promise.resolve();
    todos.value = ["a", "b", "c"];
    await Promise.resolve();
    expect(todos.value).toEqual(["a", "b", "c"]);
  });

  test("removals are visible after a write", async () => {
    const repo = makeRepo();
    const todos = $crdtList<string>("list-4", [], {
      getHandle: async () => repo.create<ListDoc<string>>({}),
    });
    await todos.loaded;
    todos.value = ["a", "b", "c"];
    await Promise.resolve();
    todos.value = ["a", "c"];
    await Promise.resolve();
    expect(todos.value).toEqual(["a", "c"]);
  });

  test("remote changes propagate back to the signal", async () => {
    const repo = makeRepo();
    const todos = $crdtList<number>("list-5", [], {
      getHandle: async () => repo.create<ListDoc<number>>({ items: [1, 2] }),
    });
    await todos.loaded;
    expect(todos.value).toEqual([1, 2]);
    (todos.handle as unknown as DocHandle<ListDoc<number>>).change((doc) => {
      doc.items = [...(doc.items ?? []), 3];
    });
    await Promise.resolve();
    expect(todos.value).toEqual([1, 2, 3]);
  });
});

describe("specialised primitives — registry integration", () => {
  test("$crdtText collides with $crdtCounter on the same key", () => {
    const repo = makeRepo();
    $crdtText("shared-key", "hello", {
      getHandle: async () => repo.create<TextDoc>({}),
    });
    expect(() =>
      $crdtCounter("shared-key", 0, {
        primitive: "meshState",
        getHandle: async () => repo.create<CounterDoc>({}),
      })
    ).toThrow();
  });

  test("each variant registers its key in the primitive registry", () => {
    const repo = makeRepo();
    $crdtText("text-key", "", {
      getHandle: async () => repo.create<TextDoc>({}),
    });
    $crdtCounter("counter-key", 0, {
      getHandle: async () => repo.create<CounterDoc>({}),
    });
    $crdtList<string>("list-key", [], {
      getHandle: async () => repo.create<ListDoc<string>>({}),
    });
    expect(primitiveRegistry.has("text-key")).toBe(true);
    expect(primitiveRegistry.has("counter-key")).toBe(true);
    expect(primitiveRegistry.has("list-key")).toBe(true);
  });
});
