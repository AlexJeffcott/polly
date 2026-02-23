import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

/**
 * Tests for $resource() extraction.
 *
 * Verifies that the handler extractor:
 * 1. Recognizes $resource() calls
 * 2. Extracts resource name and source signal reads
 * 3. Emits three synthetic handlers (FetchStart, FetchSuccess, FetchError)
 * 4. Ignores non-$resource calls
 */
describe("HandlerExtractor - $resource Discovery", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-resource-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  function createTsConfig(): string {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
          strict: true,
        },
        include: ["*.ts"],
      })
    );
    return tsConfigPath;
  }

  function createPackageJson(): void {
    fs.writeFileSync(
      path.join(tempDir, "package.json"),
      JSON.stringify({ name: "test-pkg", version: "0.0.1" })
    );
  }

  test("should detect $resource call and emit three synthetic handlers", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "resources.ts");
    fs.writeFileSync(
      testFile,
      `
function $resource<TSource, TData>(name: string, options: any) {
  return {} as any;
}
const signal = { value: { userId: "abc" } };

const todosResource = $resource("todos", {
  source: () => ({ userId: signal.value.userId }),
  fetcher: async ({ userId }: { userId: string }) => {
    return [];
  },
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    // Should have three synthetic handlers
    const resourceHandlers = result.handlers.filter((h) => h.messageType.startsWith("todos_"));
    expect(resourceHandlers.length).toBe(3);

    const types = resourceHandlers.map((h) => h.messageType).sort();
    expect(types).toEqual(["todos_FetchError", "todos_FetchStart", "todos_FetchSuccess"]);

    // Should also have the resource info
    expect(result.resources.length).toBe(1);
    expect(result.resources[0].name).toBe("todos");
    expect(result.resources[0].variableName).toBe("todosResource");
  });

  test("FetchStart handler has correct precondition and assignments", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "resources.ts");
    fs.writeFileSync(
      testFile,
      `
function $resource<TSource, TData>(name: string, options: any) {
  return {} as any;
}

const myResource = $resource("items", {
  source: () => ({}),
  fetcher: async () => [],
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    const fetchStart = result.handlers.find((h) => h.messageType === "items_FetchStart");
    expect(fetchStart).toBeDefined();
    expect(fetchStart!.preconditions.length).toBe(1);
    expect(fetchStart!.preconditions[0].expression).toBe('items_status !== "loading"');
    expect(fetchStart!.assignments).toEqual([
      { field: "items_status", value: "loading" },
      { field: "items_error", value: false },
    ]);
  });

  test("FetchSuccess handler has correct precondition and assignments", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "resources.ts");
    fs.writeFileSync(
      testFile,
      `
function $resource<TSource, TData>(name: string, options: any) {
  return {} as any;
}

const myResource = $resource("items", {
  source: () => ({}),
  fetcher: async () => [],
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    const fetchSuccess = result.handlers.find((h) => h.messageType === "items_FetchSuccess");
    expect(fetchSuccess).toBeDefined();
    expect(fetchSuccess!.preconditions.length).toBe(1);
    expect(fetchSuccess!.preconditions[0].expression).toBe('items_status === "loading"');
    expect(fetchSuccess!.assignments).toEqual([
      { field: "items_status", value: "success" },
      { field: "items_error", value: false },
    ]);
  });

  test("FetchError handler has correct precondition and assignments", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "resources.ts");
    fs.writeFileSync(
      testFile,
      `
function $resource<TSource, TData>(name: string, options: any) {
  return {} as any;
}

const myResource = $resource("items", {
  source: () => ({}),
  fetcher: async () => [],
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    const fetchError = result.handlers.find((h) => h.messageType === "items_FetchError");
    expect(fetchError).toBeDefined();
    expect(fetchError!.preconditions.length).toBe(1);
    expect(fetchError!.preconditions[0].expression).toBe('items_status === "loading"');
    expect(fetchError!.assignments).toEqual([
      { field: "items_status", value: "error" },
      { field: "items_error", value: true },
    ]);
  });

  test("should extract source signal reads", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "resources.ts");
    fs.writeFileSync(
      testFile,
      `
function $resource<TSource, TData>(name: string, options: any) {
  return {} as any;
}
const authState = { value: { userId: "abc", role: "admin" } };
const settings = { value: "dark" };

const myResource = $resource("data", {
  source: () => ({
    userId: authState.value.userId,
    role: authState.value.role,
    theme: settings.value,
  }),
  fetcher: async () => [],
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    expect(result.resources.length).toBe(1);
    const signals = result.resources[0].sourceSignals;
    expect(signals).toContain("authState_userId");
    expect(signals).toContain("authState_role");
    expect(signals).toContain("settings");
  });

  test("should not match non-$resource function calls", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "not-resource.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState(key: string, initial: any, options?: any) {
  return { value: initial };
}
function createResource(name: string, options: any) {
  return {};
}

const state = $sharedState("test", {}, { verify: true });
const res = createResource("data", {
  source: () => ({}),
  fetcher: async () => [],
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    // No resource handlers — only verified state from $sharedState
    expect(result.resources.length).toBe(0);
    const resourceHandlers = result.handlers.filter(
      (h) => h.messageType.includes("FetchStart") || h.messageType.includes("FetchSuccess")
    );
    expect(resourceHandlers.length).toBe(0);
  });

  test("message types are added to messageTypes set", () => {
    createPackageJson();
    const testFile = path.join(tempDir, "resources.ts");
    fs.writeFileSync(
      testFile,
      `
function $resource<TSource, TData>(name: string, options: any) {
  return {} as any;
}

const myResource = $resource("items", {
  source: () => ({}),
  fetcher: async () => [],
  initialValue: [],
});
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    expect(result.messageTypes.has("items_FetchStart")).toBe(true);
    expect(result.messageTypes.has("items_FetchSuccess")).toBe(true);
    expect(result.messageTypes.has("items_FetchError")).toBe(true);
  });
});
