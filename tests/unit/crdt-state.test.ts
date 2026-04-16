import { afterEach, describe, expect, test } from "bun:test";
import { Repo } from "@automerge/automerge-repo";
import { $crdtState, type CrdtStateOptions } from "@/shared/lib/crdt-state";
import { MigrationError, migrationRegistry } from "@/shared/lib/migrate-primitive";
import { PrimitiveCollisionError, primitiveRegistry } from "@/shared/lib/primitive-registry";
import { SCHEMA_VERSION_FIELD, type VersionedDoc } from "@/shared/lib/schema-version";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

const noopMigration = () => {
  /* intentionally empty — marks a version transition with no shape change */
};

function makeRepo(): Repo {
  // No storage adapter and no network adapters — pure in-memory repo.
  return new Repo();
}

function makeOptions<T extends VersionedDoc>(
  key: string,
  initialValue: T,
  extras: Partial<CrdtStateOptions<T>> = {}
): CrdtStateOptions<T> {
  const repo = makeRepo();
  return {
    key,
    primitive: "peerState",
    initialValue,
    getHandle: async () => repo.create<T>(initialValue),
    ...extras,
  };
}

afterEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

describe("$crdtState — construction", () => {
  test("returns a primitive with the supplied key and kind", () => {
    const prim = $crdtState(makeOptions<Notes>("notes-1", { title: "hello", body: "" }));
    expect(prim.key).toBe("notes-1");
    expect(prim.primitive).toBe("peerState");
  });

  test("registers the key in the primitive registry", () => {
    $crdtState(makeOptions<Notes>("notes-2", { title: "", body: "" }));
    expect(primitiveRegistry.has("notes-2")).toBe(true);
    expect(primitiveRegistry.kindOf("notes-2")).toBe("peerState");
  });

  test("exposes the initial value synchronously before loaded resolves", () => {
    const prim = $crdtState(makeOptions<Notes>("notes-3", { title: "pre-load", body: "" }));
    expect(prim.value).toEqual({ title: "pre-load", body: "" });
  });

  test("throws PrimitiveCollisionError on a cross-kind key collision", () => {
    $crdtState(makeOptions<Notes>("shared-key", { title: "", body: "" }));
    expect(() =>
      $crdtState(
        makeOptions<Notes>(
          "shared-key",
          { title: "", body: "" },
          {
            primitive: "meshState",
          }
        )
      )
    ).toThrow(PrimitiveCollisionError);
  });

  test("throws MigrationError when the key is marked as migrated", () => {
    migrationRegistry.mark("notes-4", "peerState");
    expect(() => $crdtState(makeOptions<Notes>("notes-4", { title: "", body: "" }))).toThrow(
      MigrationError
    );
  });
});

describe("$crdtState — hydration", () => {
  test("loaded resolves once the handle is ready", async () => {
    const prim = $crdtState(makeOptions<Notes>("notes-5", { title: "start", body: "" }));
    await prim.loaded;
    expect(prim.handle).toBeDefined();
    expect(prim.handle?.isReady()).toBe(true);
  });

  test("the signal reflects the hydrated document after loaded", async () => {
    const prim = $crdtState(makeOptions<Notes>("notes-6", { title: "hydrated", body: "x" }));
    await prim.loaded;
    expect(prim.value.title).toBe("hydrated");
    expect(prim.value.body).toBe("x");
  });
});

describe("$crdtState — writes", () => {
  test("assignment to value writes through to the Automerge document", async () => {
    const prim = $crdtState(makeOptions<Notes>("notes-7", { title: "", body: "" }));
    await prim.loaded;
    prim.value = { title: "updated", body: "some body" };
    // Give the effect queue a tick to flush.
    await Promise.resolve();
    const doc = prim.handle?.doc();
    expect(doc?.title).toBe("updated");
    expect(doc?.body).toBe("some body");
  });

  test("does not overwrite the reserved schema-version field", async () => {
    const prim = $crdtState(
      makeOptions<Notes>(
        "notes-8",
        { title: "", body: "" },
        { schemaVersion: 1, migrations: { 1: noopMigration } }
      )
    );
    await prim.loaded;
    prim.value = { title: "no-version", body: "" };
    await Promise.resolve();
    const doc = prim.handle?.doc() as Record<string, unknown>;
    // The version from the migration must survive the write.
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(1);
  });
});

describe("$crdtState — remote changes", () => {
  test("external handle.change calls propagate back to the signal", async () => {
    const prim = $crdtState(makeOptions<Notes>("notes-9", { title: "initial", body: "" }));
    await prim.loaded;

    // Simulate a remote change by mutating through the handle directly.
    prim.handle?.change((doc) => {
      (doc as unknown as Notes).title = "changed-by-remote";
    });
    await Promise.resolve();

    expect(prim.value.title).toBe("changed-by-remote");
  });
});

describe("$crdtState — schema migrations", () => {
  test("runs migrations on load up to the target version", async () => {
    type V2 = VersionedDoc & { title: string; tags: string[] };
    // Use a single-repo factory so the "create with initialValue" happens
    // once and migrations run against it.
    const repo = makeRepo();
    let handleRef: any = null;
    const prim = $crdtState<V2>({
      key: "doc-v2",
      primitive: "peerState",
      initialValue: { title: "", tags: [] },
      schemaVersion: 2,
      migrations: {
        1: (doc) => {
          doc["title"] = "migrated-v1";
        },
        2: (doc) => {
          doc["tags"] = ["migrated-v2"];
        },
      },
      getHandle: async () => {
        // Create with a bare doc (no title/tags) so the migrations do work.
        handleRef = repo.create<V2>({} as unknown as V2);
        return handleRef;
      },
    });
    await prim.loaded;
    expect(prim.value.title).toBe("migrated-v1");
    expect(prim.value.tags).toEqual(["migrated-v2"]);
    const doc = prim.handle?.doc() as Record<string, unknown>;
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(2);
  });

  test("stamps the target version even when no migrations run", async () => {
    const repo = makeRepo();
    const prim = $crdtState<Notes>({
      key: "doc-already-v3",
      primitive: "peerState",
      initialValue: { title: "", body: "" },
      schemaVersion: 3,
      migrations: {
        1: noopMigration,
        2: noopMigration,
        3: noopMigration,
      },
      getHandle: async () => {
        // Pre-stamp the doc at v3 so runMigrations is a no-op but setDocVersion
        // still records the target.
        const handle = repo.create<Notes>({
          title: "existing",
          body: "",
          [SCHEMA_VERSION_FIELD]: 3,
        } as unknown as Notes);
        return handle;
      },
    });
    await prim.loaded;
    const doc = prim.handle?.doc() as Record<string, unknown>;
    expect(doc[SCHEMA_VERSION_FIELD]).toBe(3);
    expect(prim.value.title).toBe("existing");
  });
});
