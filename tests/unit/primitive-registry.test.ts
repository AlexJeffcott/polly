import { beforeEach, describe, expect, test } from "bun:test";
import {
  PrimitiveCollisionError,
  PrimitiveRegistry,
  primitiveRegistry,
} from "@/shared/lib/primitive-registry";

describe("PrimitiveRegistry", () => {
  let registry: PrimitiveRegistry;

  beforeEach(() => {
    registry = new PrimitiveRegistry();
  });

  test("registers a new key without throwing", () => {
    expect(() => registry.register("notes", "peerState")).not.toThrow();
    expect(registry.has("notes")).toBe(true);
    expect(registry.size).toBe(1);
  });

  test("reports the kind of a registered key", () => {
    registry.register("notes", "peerState");
    expect(registry.kindOf("notes")).toBe("peerState");
  });

  test("reports undefined for an unregistered key", () => {
    expect(registry.kindOf("missing")).toBeUndefined();
  });

  test("has() returns false for an unregistered key", () => {
    expect(registry.has("missing")).toBe(false);
  });

  test("re-registering the same key under the same primitive is a no-op", () => {
    registry.register("notes", "peerState", "src/a.ts:10");
    expect(() => registry.register("notes", "peerState", "src/b.ts:20")).not.toThrow();
    expect(registry.size).toBe(1);
    // The first call site is preserved (no clobber on idempotent re-register).
    expect(registry.kindOf("notes")).toBe("peerState");
  });

  test("registering the same key under a different primitive throws", () => {
    registry.register("notes", "peerState");
    expect(() => registry.register("notes", "meshState")).toThrow(PrimitiveCollisionError);
  });

  test("the collision error names the key", () => {
    registry.register("notes", "peerState");
    try {
      registry.register("notes", "meshState");
      throw new Error("should have thrown");
    } catch (err) {
      expect(err).toBeInstanceOf(PrimitiveCollisionError);
      const collision = err as PrimitiveCollisionError;
      expect(collision.key).toBe("notes");
    }
  });

  test("the collision error names both primitives", () => {
    registry.register("notes", "peerState");
    try {
      registry.register("notes", "meshState");
      throw new Error("should have thrown");
    } catch (err) {
      const collision = err as PrimitiveCollisionError;
      expect(collision.firstPrimitive).toBe("peerState");
      expect(collision.secondPrimitive).toBe("meshState");
    }
  });

  test("the collision error names both call sites when supplied", () => {
    registry.register("notes", "peerState", "src/one.ts:10");
    try {
      registry.register("notes", "meshState", "src/two.ts:20");
      throw new Error("should have thrown");
    } catch (err) {
      const collision = err as PrimitiveCollisionError;
      expect(collision.firstCallSite).toBe("src/one.ts:10");
      expect(collision.secondCallSite).toBe("src/two.ts:20");
      expect(collision.message).toContain("src/one.ts:10");
      expect(collision.message).toContain("src/two.ts:20");
      expect(collision.message).toContain("peerState");
      expect(collision.message).toContain("meshState");
      expect(collision.message).toContain("notes");
    }
  });

  test("the collision error has name 'PrimitiveCollisionError'", () => {
    registry.register("x", "peerState");
    try {
      registry.register("x", "meshState");
      throw new Error("should have thrown");
    } catch (err) {
      expect((err as Error).name).toBe("PrimitiveCollisionError");
    }
  });

  test("the collision error is an Error subclass", () => {
    registry.register("x", "peerState");
    try {
      registry.register("x", "meshState");
      throw new Error("should have thrown");
    } catch (err) {
      expect(err).toBeInstanceOf(Error);
      expect(err).toBeInstanceOf(PrimitiveCollisionError);
    }
  });

  test("collisions between $sharedState and $peerState throw", () => {
    registry.register("settings", "sharedState");
    expect(() => registry.register("settings", "peerState")).toThrow(PrimitiveCollisionError);
  });

  test("collisions between $peerState and $meshState throw", () => {
    registry.register("doc", "peerState");
    expect(() => registry.register("doc", "meshState")).toThrow(PrimitiveCollisionError);
  });

  test("unrelated keys do not collide", () => {
    registry.register("a", "sharedState");
    registry.register("b", "peerState");
    registry.register("c", "meshState");
    expect(registry.size).toBe(3);
    expect(registry.kindOf("a")).toBe("sharedState");
    expect(registry.kindOf("b")).toBe("peerState");
    expect(registry.kindOf("c")).toBe("meshState");
  });

  test("clear() drops every registration", () => {
    registry.register("a", "peerState");
    registry.register("b", "meshState");
    expect(registry.size).toBe(2);
    registry.clear();
    expect(registry.size).toBe(0);
    expect(registry.has("a")).toBe(false);
    expect(registry.has("b")).toBe(false);
  });

  test("a key can be reused after clear()", () => {
    registry.register("notes", "peerState");
    registry.clear();
    expect(() => registry.register("notes", "meshState")).not.toThrow();
    expect(registry.kindOf("notes")).toBe("meshState");
  });
});

describe("primitiveRegistry singleton", () => {
  beforeEach(() => {
    primitiveRegistry.clear();
  });

  test("is the same instance across imports", () => {
    primitiveRegistry.register("global-test", "peerState");
    expect(primitiveRegistry.has("global-test")).toBe(true);
    expect(primitiveRegistry.kindOf("global-test")).toBe("peerState");
  });

  test("enforces collisions the same way as a fresh instance", () => {
    primitiveRegistry.register("shared-key", "sharedState");
    expect(() => primitiveRegistry.register("shared-key", "meshState")).toThrow(
      PrimitiveCollisionError
    );
  });
});
