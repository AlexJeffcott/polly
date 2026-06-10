import { describe, expect, test } from "bun:test";
import {
  extractRouteParams,
  findMatchingConfig,
  findMatchingEntry,
  matchRoute,
} from "@/elysia/route-match";

describe("matchRoute", () => {
  test("exact method + path", () => {
    expect(matchRoute("POST /todos", "POST", "/todos")).toBe(true);
    expect(matchRoute("POST /todos", "GET", "/todos")).toBe(false);
    expect(matchRoute("POST /todos", "POST", "/todos/1")).toBe(false);
  });

  test("param segments match any value", () => {
    expect(matchRoute("PATCH /todos/:id", "PATCH", "/todos/42")).toBe(true);
    expect(matchRoute("PATCH /todos/:id", "PATCH", "/todos")).toBe(false);
  });

  test("wildcard matches the rest of the path", () => {
    expect(matchRoute("/todos/*", "GET", "/todos/a/b")).toBe(true);
    expect(matchRoute("/todos/*", "DELETE", "/todos/a/b")).toBe(true);
  });

  test("pattern without a method matches any method", () => {
    expect(matchRoute("/todos", "GET", "/todos")).toBe(true);
    expect(matchRoute("/todos", "POST", "/todos")).toBe(true);
  });
});

describe("findMatchingEntry", () => {
  const configs = {
    "POST /todos": "create",
    "PATCH /todos/:id": "update",
    "DELETE /todos/:id": "remove",
  };

  test("returns the pattern and config of the first match", () => {
    expect(findMatchingEntry(configs, "PATCH", "/todos/7")).toEqual({
      pattern: "PATCH /todos/:id",
      config: "update",
    });
  });

  test("returns undefined when nothing matches or configs is missing", () => {
    expect(findMatchingEntry(configs, "PUT", "/todos/7")).toBeUndefined();
    expect(findMatchingEntry(undefined, "POST", "/todos")).toBeUndefined();
  });

  test("findMatchingConfig is the config half of findMatchingEntry", () => {
    expect(findMatchingConfig(configs, "POST", "/todos")).toBe("create");
    expect(findMatchingConfig(configs, "POST", "/nope")).toBeUndefined();
  });
});

describe("extractRouteParams", () => {
  test("extracts named params from a concrete path", () => {
    expect(extractRouteParams("PATCH /todos/:id", "/todos/5")).toEqual({ id: "5" });
    expect(extractRouteParams("GET /a/:x/b/:y", "/a/1/b/2")).toEqual({ x: "1", y: "2" });
  });

  test("works without a method prefix", () => {
    expect(extractRouteParams("/todos/:id", "/todos/9")).toEqual({ id: "9" });
  });

  test("no params yields an empty object", () => {
    expect(extractRouteParams("POST /todos", "/todos")).toEqual({});
  });
});
