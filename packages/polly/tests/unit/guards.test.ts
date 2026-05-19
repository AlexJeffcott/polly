import { describe, expect, test } from "bun:test";
import { hasKeyInObject, isRecord } from "@/shared/lib/guards";

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
