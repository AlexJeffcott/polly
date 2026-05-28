import { describe, expect, test } from "bun:test";
import { assertNever, hasKeyInObject, isRecord } from "@/shared/lib/guards";

describe("isRecord", () => {
  test("returns true for plain objects", () => {
    expect(isRecord({})).toBe(true);
    expect(isRecord({ a: 1 })).toBe(true);
  });

  test("returns false for arrays", () => {
    expect(isRecord([])).toBe(false);
    expect(isRecord([1, 2, 3])).toBe(false);
  });

  test("returns false for null", () => {
    expect(isRecord(null)).toBe(false);
  });

  test("returns false for primitives", () => {
    expect(isRecord("string")).toBe(false);
    expect(isRecord(42)).toBe(false);
    expect(isRecord(true)).toBe(false);
    expect(isRecord(undefined)).toBe(false);
  });
});

describe("hasKeyInObject", () => {
  test("returns true for own properties", () => {
    expect(hasKeyInObject({ a: 1 }, "a")).toBe(true);
    expect(hasKeyInObject({ nested: { b: 2 } }, "nested")).toBe(true);
  });

  test("returns true for own properties whose value is undefined", () => {
    // Object.hasOwn distinguishes "key absent" from "key present with undefined".
    expect(hasKeyInObject({ a: undefined }, "a")).toBe(true);
  });

  test("returns false for keys on the prototype chain", () => {
    expect(hasKeyInObject({}, "toString")).toBe(false);
    expect(hasKeyInObject({}, "hasOwnProperty")).toBe(false);
  });

  test("returns false for absent keys", () => {
    expect(hasKeyInObject({ a: 1 }, "b")).toBe(false);
  });

  test("returns false for null", () => {
    expect(hasKeyInObject(null, "a")).toBe(false);
  });

  test("returns false for primitives", () => {
    expect(hasKeyInObject("string", "length")).toBe(false);
    expect(hasKeyInObject(42, "toString")).toBe(false);
    expect(hasKeyInObject(undefined, "a")).toBe(false);
  });
});

describe("assertNever", () => {
  type Shape = { kind: "a"; a: number } | { kind: "b"; b: string };

  function describeShape(shape: Shape): string {
    switch (shape.kind) {
      case "a":
        return `a:${shape.a}`;
      case "b":
        return `b:${shape.b}`;
      default:
        // Compiles only because every variant above is handled — `shape` is
        // `never` here. This line is the exhaustiveness guarantee.
        return assertNever(shape);
    }
  }

  test("an exhaustive switch routes each variant without throwing", () => {
    expect(describeShape({ kind: "a", a: 1 })).toBe("a:1");
    expect(describeShape({ kind: "b", b: "x" })).toBe("b:x");
  });

  test("throws when reached at runtime with an out-of-union value", () => {
    // A value smuggled past the type system (e.g. a malformed parsed payload).
    const rogue = { kind: "c" } as unknown as never;
    expect(() => assertNever(rogue)).toThrow(/unexpected value/);
    expect(() => assertNever(rogue)).toThrow(/"kind":"c"/);
  });

  test("rejects a still-inhabited value at compile time", () => {
    const stillB: { kind: "b" } = { kind: "b" };
    // @ts-expect-error — `stillB` is not `never`, so the missing-case guard
    // fires. If assertNever's parameter were widened, this directive would
    // become unused and `tsc` (the project typecheck) would fail.
    expect(() => assertNever(stillB)).toThrow();
  });
});
