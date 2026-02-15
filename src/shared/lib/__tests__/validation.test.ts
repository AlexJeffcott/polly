/**
 * Tests for DX Enhancement #4: Validation Helpers
 *
 * Tests validateShape(), validateEnum(), validateArray(), and validatePartial()
 */

import { describe, expect, test } from "bun:test";
import { validateArray, validateEnum, validatePartial, validateShape } from "../validation";

describe("validateShape", () => {
  test("should validate simple object shapes", () => {
    type User = {
      name: string;
      age: number;
      active: boolean;
    };

    const isUser = validateShape<User>({
      name: "string",
      age: "number",
      active: "boolean",
    });

    expect(isUser({ name: "Alice", age: 30, active: true })).toBe(true);
    expect(isUser({ name: "Bob", age: 25, active: false })).toBe(true);
  });

  test("should reject objects with wrong types", () => {
    type Settings = {
      theme: string;
      count: number;
    };

    const isSettings = validateShape<Settings>({
      theme: "string",
      count: "number",
    });

    expect(isSettings({ theme: "dark", count: "5" })).toBe(false); // count is string
    expect(isSettings({ theme: 123, count: 5 })).toBe(false); // theme is number
  });

  test("should reject objects with missing fields", () => {
    type Config = {
      apiKey: string;
      timeout: number;
    };

    const isConfig = validateShape<Config>({
      apiKey: "string",
      timeout: "number",
    });

    expect(isConfig({ apiKey: "key123" })).toBe(false); // missing timeout
    expect(isConfig({ timeout: 5000 })).toBe(false); // missing apiKey
    expect(isConfig({})).toBe(false); // missing both
  });

  test("should validate arrays", () => {
    type Data = {
      items: any[];
    };

    const isData = validateShape<Data>({
      items: "array",
    });

    expect(isData({ items: [] })).toBe(true);
    expect(isData({ items: [1, 2, 3] })).toBe(true);
    expect(isData({ items: ["a", "b"] })).toBe(true);
    expect(isData({ items: "not an array" })).toBe(false);
    expect(isData({ items: null })).toBe(false);
  });

  test("should validate null values", () => {
    type NullableData = {
      value: null;
    };

    const isNullableData = validateShape<NullableData>({
      value: "null",
    });

    expect(isNullableData({ value: null })).toBe(true);
    expect(isNullableData({ value: undefined })).toBe(false);
    expect(isNullableData({ value: 0 })).toBe(false);
  });

  test("should validate undefined values", () => {
    type OptionalData = {
      value: undefined;
    };

    const isOptionalData = validateShape<OptionalData>({
      value: "undefined",
    });

    expect(isOptionalData({ value: undefined })).toBe(true);
    expect(isOptionalData({ value: null })).toBe(false);
    expect(isOptionalData({ value: 0 })).toBe(false);
  });

  test("should validate nested objects", () => {
    type User = {
      profile: {
        name: string;
        age: number;
      };
    };

    const isUser = validateShape<User>({
      profile: {
        name: "string",
        age: "number",
      },
    });

    expect(isUser({ profile: { name: "Alice", age: 30 } })).toBe(true);
    expect(isUser({ profile: { name: "Bob", age: "25" } })).toBe(false); // age is string
    expect(isUser({ profile: { name: "Charlie" } })).toBe(false); // missing age
    expect(isUser({ profile: "not an object" })).toBe(false);
  });

  test("should reject non-objects", () => {
    const isShape = validateShape<{ name: string }>({
      name: "string",
    });

    expect(isShape(null)).toBe(false);
    expect(isShape(undefined)).toBe(false);
    expect(isShape("string")).toBe(false);
    expect(isShape(123)).toBe(false);
    expect(isShape([])).toBe(false);
  });

  test("should validate complex nested structures", () => {
    type AppState = {
      user: {
        name: string;
        age: number;
      };
      settings: {
        theme: string;
        notifications: boolean;
      };
    };

    const isAppState = validateShape<AppState>({
      user: {
        name: "string",
        age: "number",
      },
      settings: {
        theme: "string",
        notifications: "boolean",
      },
    });

    expect(
      isAppState({
        user: { name: "Alice", age: 30 },
        settings: { theme: "dark", notifications: true },
      })
    ).toBe(true);

    expect(
      isAppState({
        user: { name: "Alice", age: 30 },
        settings: { theme: "dark" }, // missing notifications
      })
    ).toBe(false);
  });
});

describe("validateEnum", () => {
  test("should validate string enums", () => {
    type Theme = "light" | "dark" | "auto";

    const isTheme = validateEnum<Theme>(["light", "dark", "auto"]);

    expect(isTheme("light")).toBe(true);
    expect(isTheme("dark")).toBe(true);
    expect(isTheme("auto")).toBe(true);
    expect(isTheme("invalid")).toBe(false);
    expect(isTheme(null)).toBe(false);
    expect(isTheme(undefined)).toBe(false);
  });

  test("should validate number enums", () => {
    type Status = 1 | 2 | 3;

    const isStatus = validateEnum<Status>([1, 2, 3]);

    expect(isStatus(1)).toBe(true);
    expect(isStatus(2)).toBe(true);
    expect(isStatus(3)).toBe(true);
    expect(isStatus(4)).toBe(false);
    expect(isStatus("1")).toBe(false);
  });

  test("should handle empty arrays", () => {
    const isEmpty = validateEnum([]);

    expect(isEmpty("anything")).toBe(false);
    expect(isEmpty(null)).toBe(false);
  });

  test("should handle single value enums", () => {
    type Single = "only";

    const isSingle = validateEnum<Single>(["only"]);

    expect(isSingle("only")).toBe(true);
    expect(isSingle("other")).toBe(false);
  });
});

describe("validateArray", () => {
  test("should validate arrays of strings", () => {
    const isStringArray = validateArray<string>((v): v is string => typeof v === "string");

    expect(isStringArray(["a", "b", "c"])).toBe(true);
    expect(isStringArray([])).toBe(true);
    expect(isStringArray(["a", 1, "c"])).toBe(false); // mixed types
    expect(isStringArray("not an array")).toBe(false);
  });

  test("should validate arrays of numbers", () => {
    const isNumberArray = validateArray<number>((v): v is number => typeof v === "number");

    expect(isNumberArray([1, 2, 3])).toBe(true);
    expect(isNumberArray([])).toBe(true);
    expect(isNumberArray([1, "2", 3])).toBe(false); // mixed types
  });

  test("should validate arrays of complex objects", () => {
    type User = { name: string; age: number };

    const isUser = (v: unknown): v is User => {
      return (
        typeof v === "object" &&
        v !== null &&
        "name" in v &&
        typeof (v as any).name === "string" &&
        "age" in v &&
        typeof (v as any).age === "number"
      );
    };

    const isUserArray = validateArray<User>(isUser);

    expect(
      isUserArray([
        { name: "Alice", age: 30 },
        { name: "Bob", age: 25 },
      ])
    ).toBe(true);

    expect(
      isUserArray([
        { name: "Alice", age: 30 },
        { name: "Bob" }, // missing age
      ])
    ).toBe(false);
  });

  test("should reject non-arrays", () => {
    const isStringArray = validateArray<string>((v): v is string => typeof v === "string");

    expect(isStringArray(null)).toBe(false);
    expect(isStringArray(undefined)).toBe(false);
    expect(isStringArray("string")).toBe(false);
    expect(isStringArray({ 0: "a", 1: "b" })).toBe(false); // object that looks like array
  });

  test("should handle empty arrays", () => {
    const isStringArray = validateArray<string>((v): v is string => typeof v === "string");

    expect(isStringArray([])).toBe(true);
  });
});

describe("validatePartial", () => {
  test("should accept partial objects", () => {
    type Settings = {
      theme: string;
      autoSync: boolean;
      debugMode: boolean;
    };

    const isSettings = validateShape<Settings>({
      theme: "string",
      autoSync: "boolean",
      debugMode: "boolean",
    });

    const isPartialSettings = validatePartial(isSettings);

    // Any object should pass (simplified implementation)
    expect(isPartialSettings({ theme: "dark" })).toBe(true);
    expect(isPartialSettings({ autoSync: true })).toBe(true);
    expect(isPartialSettings({ theme: "dark", autoSync: true })).toBe(true);
    expect(isPartialSettings({})).toBe(true);
  });

  test("should reject non-objects", () => {
    const isSettings = validateShape<{ theme: string }>({
      theme: "string",
    });

    const isPartialSettings = validatePartial(isSettings);

    expect(isPartialSettings(null)).toBe(false);
    expect(isPartialSettings(undefined)).toBe(false);
    expect(isPartialSettings("string")).toBe(false);
    expect(isPartialSettings(123)).toBe(false);
  });
});

describe("Integration: Using validators with $sharedState", () => {
  test("validateShape can be used as state validator", () => {
    type Settings = {
      theme: string;
      count: number;
    };

    const validator = validateShape<Settings>({
      theme: "string",
      count: "number",
    });

    // Should validate correct objects
    expect(validator({ theme: "dark", count: 5 })).toBe(true);

    // Should reject invalid objects
    expect(validator({ theme: "dark" })).toBe(false); // missing count
    expect(validator({ theme: 123, count: 5 })).toBe(false); // wrong type
  });

  test("validateEnum can validate state transitions", () => {
    type ConnectionState = "disconnected" | "connecting" | "connected";

    const isConnectionState = validateEnum<ConnectionState>([
      "disconnected",
      "connecting",
      "connected",
    ]);

    expect(isConnectionState("disconnected")).toBe(true);
    expect(isConnectionState("connecting")).toBe(true);
    expect(isConnectionState("connected")).toBe(true);
    expect(isConnectionState("invalid")).toBe(false);
  });
});
