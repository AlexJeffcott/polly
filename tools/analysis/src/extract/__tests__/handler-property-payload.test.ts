// Tests for payload-property tracing in regular property assignments.
//
// When a handler writes `{ field: paramName.X }` into a signal — the longhand
// equivalent of the shorthand `{ field }` form — the extractor records
// `{ field, value: "param:X" }`. This is the marker the verify-tool consumes to
// type the payload field by the modeled state field's domain (issue #72) and
// to wrap ensures() postconditions in TLC Assert (issue #73).

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("HandlerExtractor — payload-property tracing in object literals", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-pp-test-"));
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
        compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
        include: ["*.ts"],
      })
    );
    fs.writeFileSync(
      path.join(tempDir, "package.json"),
      JSON.stringify({ name: "test-pkg", version: "0.0.1" })
    );
    return tsConfigPath;
  }

  function writeHandlerFile(body: string): void {
    fs.writeFileSync(
      path.join(tempDir, "handlers.ts"),
      `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare const bus: {
  on: <T>(type: string, fn: (payload: T) => void) => void;
};

const user = $sharedState("user", { loggedIn: false, role: "guest" as string });

${body}
`
    );
  }

  test("longhand `{ field: paramName.X }` produces a param:X marker", () => {
    writeHandlerFile(`
bus.on<{ role: string }>("USER_SET_ROLE", (payload) => {
  user.value = { ...user.value, role: payload.role };
});
`);
    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    const handler = result.handlers.find((h) => h.messageType === "USER_SET_ROLE");
    expect(handler).toBeDefined();
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([{ field: "user_role", value: "param:role" }])
    );
  });

  test("longhand with renamed property still resolves payload identifier", () => {
    // Property is named differently from the payload field it pulls from:
    // `role: payload.kind` → field is "user_role", payload field is "kind".
    writeHandlerFile(`
bus.on<{ kind: string }>("USER_SET_KIND", (payload) => {
  user.value = { ...user.value, role: payload.kind };
});
`);
    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    const handler = result.handlers.find((h) => h.messageType === "USER_SET_KIND");
    expect(handler).toBeDefined();
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([{ field: "user_role", value: "param:kind" }])
    );
  });

  test("non-payload property access (`other.x`) does NOT produce a marker", () => {
    // The RHS must come from a function parameter; arbitrary property access
    // (e.g. another module-scope object) is not surfaced as a payload field.
    writeHandlerFile(`
const other = { value: { kind: "guest" } };
bus.on<{}>("USE_OTHER", () => {
  user.value = { ...user.value, role: other.value.kind };
});
`);
    const extractor = new HandlerExtractor(createTsConfig());
    const result = extractor.extractHandlers();

    const handler = result.handlers.find((h) => h.messageType === "USE_OTHER");
    expect(handler).toBeDefined();
    const paramAssignments = handler!.assignments.filter(
      (a) => typeof a.value === "string" && a.value.startsWith("param:")
    );
    expect(paramAssignments).toEqual([]);
  });
});
