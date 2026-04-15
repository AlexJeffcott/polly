import { beforeEach, describe, expect, test } from "bun:test";
import {
  type MigratableState,
  MigrationError,
  MigrationRegistry,
  migratePrimitive,
  migrationRegistry,
} from "@/shared/lib/migrate-primitive";
import type { PrimitiveKind } from "@/shared/lib/primitive-registry";

function makeState<T>(key: string, primitive: PrimitiveKind, initial: T): MigratableState<T> {
  return {
    key,
    primitive,
    value: initial,
    loaded: Promise.resolve(),
  };
}

describe("MigrationRegistry", () => {
  let registry: MigrationRegistry;

  beforeEach(() => {
    registry = new MigrationRegistry();
  });

  test("isMarked returns false before any mark", () => {
    expect(registry.isMarked("notes", "sharedState")).toBe(false);
  });

  test("mark then isMarked returns true", () => {
    registry.mark("notes", "sharedState");
    expect(registry.isMarked("notes", "sharedState")).toBe(true);
  });

  test("marks are per (key, primitive) pair", () => {
    registry.mark("notes", "sharedState");
    expect(registry.isMarked("notes", "peerState")).toBe(false);
    expect(registry.isMarked("other", "sharedState")).toBe(false);
  });

  test("mark is idempotent", () => {
    registry.mark("notes", "sharedState");
    registry.mark("notes", "sharedState");
    expect(registry.size).toBe(1);
  });

  test("clear drops every mark", () => {
    registry.mark("a", "sharedState");
    registry.mark("b", "peerState");
    expect(registry.size).toBe(2);
    registry.clear();
    expect(registry.size).toBe(0);
    expect(registry.isMarked("a", "sharedState")).toBe(false);
  });
});

describe("migratePrimitive", () => {
  beforeEach(() => {
    migrationRegistry.clear();
  });

  test("copies the transformed value from source to destination", async () => {
    const source = makeState("notes", "sharedState", { items: [1, 2, 3] });
    const dest = makeState("notes", "meshState", { entries: [] as number[] });
    await migratePrimitive(source, dest, (v) => ({ entries: v.items }));
    expect(dest.value).toEqual({ entries: [1, 2, 3] });
  });

  test("awaits loaded on both source and destination", async () => {
    let sourceLoaded = false;
    let destLoaded = false;
    const source: MigratableState<number> = {
      key: "n",
      primitive: "sharedState",
      value: 5,
      loaded: Promise.resolve().then(() => {
        sourceLoaded = true;
      }),
    };
    const dest: MigratableState<number> = {
      key: "n",
      primitive: "peerState",
      value: 0,
      loaded: Promise.resolve().then(() => {
        destLoaded = true;
      }),
    };
    await migratePrimitive(source, dest, (v) => v * 2);
    expect(sourceLoaded).toBe(true);
    expect(destLoaded).toBe(true);
    expect(dest.value).toBe(10);
  });

  test("marks the source as migrated after a successful migration", async () => {
    const source = makeState("notes", "sharedState", "hello");
    const dest = makeState("notes", "peerState", "");
    await migratePrimitive(source, dest, (v) => v.toUpperCase());
    expect(migrationRegistry.isMarked("notes", "sharedState")).toBe(true);
    expect(migrationRegistry.isMarked("notes", "peerState")).toBe(false);
  });

  test("throws when the source has already been migrated", async () => {
    const source = makeState("notes", "sharedState", 1);
    const dest = makeState("notes", "peerState", 0);
    await migratePrimitive(source, dest, (v) => v + 1);

    const secondDest = makeState("notes", "meshState", 0);
    let caught: unknown;
    try {
      await migratePrimitive(source, secondDest, (v) => v + 100);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(MigrationError);
    const error = caught as MigrationError;
    expect(error.code).toBe("already-migrated");
    expect(error.key).toBe("notes");
    expect(error.primitive).toBe("sharedState");
    // The destination from the second attempt is untouched.
    expect(secondDest.value).toBe(0);
  });

  test("throws when source and destination are the same object", async () => {
    const state = makeState("notes", "peerState", { count: 0 });
    let caught: unknown;
    try {
      await migratePrimitive(state, state, (v) => v);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(MigrationError);
    const error = caught as MigrationError;
    expect(error.code).toBe("same-primitive-instance");
  });

  test("applies the transform exactly once", async () => {
    let calls = 0;
    const source = makeState("notes", "sharedState", 5);
    const dest = makeState("notes", "peerState", 0);
    await migratePrimitive(source, dest, (v) => {
      calls += 1;
      return v * 10;
    });
    expect(calls).toBe(1);
    expect(dest.value).toBe(50);
  });

  test("supports migrations between distinct key names", async () => {
    const source = makeState("old-notes", "sharedState", { text: "hello" });
    const dest = makeState("new-notes", "peerState", { content: "" });
    await migratePrimitive(source, dest, (v) => ({ content: v.text }));
    expect(dest.value).toEqual({ content: "hello" });
    expect(migrationRegistry.isMarked("old-notes", "sharedState")).toBe(true);
    expect(migrationRegistry.isMarked("new-notes", "peerState")).toBe(false);
  });

  test("two different sources with the same key but different kinds can both migrate", async () => {
    const sharedSource = makeState("notes", "sharedState", 1);
    const sharedDest = makeState("notes-1", "peerState", 0);
    await migratePrimitive(sharedSource, sharedDest, (v) => v + 1);

    const peerSource = makeState("notes", "peerState", 10);
    const peerDest = makeState("notes-2", "meshState", 0);
    await migratePrimitive(peerSource, peerDest, (v) => v + 1);

    expect(migrationRegistry.isMarked("notes", "sharedState")).toBe(true);
    expect(migrationRegistry.isMarked("notes", "peerState")).toBe(true);
    expect(migrationRegistry.size).toBe(2);
  });
});
