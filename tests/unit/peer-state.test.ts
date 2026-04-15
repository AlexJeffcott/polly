import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { Repo } from "@automerge/automerge-repo";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import {
  $peerCounter,
  $peerList,
  $peerState,
  $peerText,
  configurePeerState,
  resetPeerState,
} from "@/shared/lib/peer-state";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";
import type { VersionedDoc } from "@/shared/lib/schema-version";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

beforeEach(() => {
  configurePeerState(new Repo());
});

afterEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
  resetPeerState();
});

describe("$peerState — construction", () => {
  test("registers the key as peerState", () => {
    $peerState<Notes>("notes-1", { title: "", body: "" });
    expect(primitiveRegistry.kindOf("notes-1")).toBe("peerState");
  });

  test("exposes the initial value synchronously", () => {
    const prim = $peerState<Notes>("notes-2", { title: "hello", body: "" });
    expect(prim.value).toEqual({ title: "hello", body: "" });
  });

  test("hydrates from the configured Repo", async () => {
    const prim = $peerState<Notes>("notes-3", { title: "from-init", body: "" });
    await prim.loaded;
    expect(prim.value.title).toBe("from-init");
    expect(prim.handle).toBeDefined();
  });
});

describe("$peerState — repo configuration", () => {
  test("throws when no Repo is configured", () => {
    resetPeerState();
    expect(() => $peerState<Notes>("notes-4", { title: "", body: "" })).toThrow(
      /no Repo configured/i
    );
  });

  test("accepts a per-call repo override", () => {
    resetPeerState();
    const repo = new Repo();
    const prim = $peerState<Notes>("notes-5", { title: "override", body: "" }, { repo });
    expect(prim.value.title).toBe("override");
  });
});

describe("$peerState — encrypt/sign deferral", () => {
  test("throws on { encrypt: true }", () => {
    expect(() => $peerState<Notes>("notes-6", { title: "", body: "" }, { encrypt: true })).toThrow(
      /Phase 2 crypto layer/
    );
  });

  test("throws on { sign: true }", () => {
    expect(() => $peerState<Notes>("notes-7", { title: "", body: "" }, { sign: true })).toThrow(
      /Phase 2 crypto layer/
    );
  });
});

describe("$peerState — writes propagate", () => {
  test("local writes appear on the underlying handle", async () => {
    const prim = $peerState<Notes>("notes-8", { title: "", body: "" });
    await prim.loaded;
    prim.value = { title: "written", body: "body" };
    await Promise.resolve();
    expect(prim.handle?.doc().title).toBe("written");
    expect(prim.handle?.doc().body).toBe("body");
  });
});

describe("$peerText / $peerCounter / $peerList", () => {
  test("$peerText round-trips through the handle", async () => {
    const text = $peerText("text-1", "hello");
    await text.loaded;
    text.value = "world";
    await Promise.resolve();
    expect(text.value).toBe("world");
    expect(primitiveRegistry.kindOf("text-1")).toBe("peerState");
  });

  test("$peerCounter round-trips through the handle", async () => {
    const counter = $peerCounter("counter-1", 0);
    await counter.loaded;
    counter.value += 1;
    await Promise.resolve();
    counter.value += 1;
    await Promise.resolve();
    expect(counter.value).toBe(2);
    expect(primitiveRegistry.kindOf("counter-1")).toBe("peerState");
  });

  test("$peerList round-trips through the handle", async () => {
    const todos = $peerList<string>("list-1", []);
    await todos.loaded;
    todos.value = ["a", "b"];
    await Promise.resolve();
    expect(todos.value).toEqual(["a", "b"]);
    expect(primitiveRegistry.kindOf("list-1")).toBe("peerState");
  });

  test("specialised variants throw on encrypt/sign", () => {
    expect(() => $peerText("t", "", { encrypt: true })).toThrow();
    expect(() => $peerCounter("c", 0, { sign: true })).toThrow();
    expect(() => $peerList<string>("l", [], { encrypt: true })).toThrow();
  });
});

describe("$peerState — key→DocumentId mapping", () => {
  test("two primitives sharing a key on the same Repo find the same document", async () => {
    const repo = new Repo();
    configurePeerState(repo);

    const a = $peerState<Notes>("shared-doc", { title: "first", body: "" });
    await a.loaded;
    a.value = { title: "written by a", body: "" };
    await Promise.resolve();

    // Reset only the primitive registry so we can register the same key again
    // in this test. (The doc-id map persists in the Repo's WeakMap, so the
    // second registration should find the same document.)
    primitiveRegistry.clear();

    const b = $peerState<Notes>("shared-doc", { title: "ignored", body: "" });
    await b.loaded;
    expect(b.value.title).toBe("written by a");
    expect(b.handle?.documentId).toBe(a.handle?.documentId);
  });
});
