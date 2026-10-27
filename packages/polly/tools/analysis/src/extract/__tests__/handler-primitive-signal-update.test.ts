// A numeric update to a primitive signal — `bookmarkCount.value++` or
// `bookmarkCount.value += 2` — used to be dropped: the `++`/`+=` paths knew
// `state.f` and `s.value.f` but not `s.value`, which a literal write to the
// same signal already maps to field `s`. The handler's action became an
// UNCHANGED stub, so examples/full-featured's BOOKMARK_ADD broke its own
// `ensures(bookmarkCount.value > 0)` in the model and nowhere else.

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("HandlerExtractor — numeric update of a primitive signal", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-prim-signal-test-"));
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

  async function assignmentsOf(messageType: string, body: string) {
    fs.writeFileSync(
      path.join(tempDir, "handlers.ts"),
      `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare const bus: {
  on: <T>(type: string, fn: (payload: T) => void) => void;
};

const bookmarkCount = $sharedState("bookmarkCount", 0);
const session = $sharedState("session", { outstanding: 0 });

${body}
`
    );
    const result = await new HandlerExtractor(createTsConfig()).extractHandlers();
    return result.handlers.find((h) => h.messageType === messageType)?.assignments;
  }

  test("`count.value++` writes the signal's own field", async () => {
    const assignments = await assignmentsOf(
      "ADD",
      `bus.on("ADD", () => { bookmarkCount.value++; });`
    );
    expect(assignments).toEqual([{ field: "bookmarkCount", value: "@ + 1" }]);
  });

  test("`--count.value` writes the signal's own field", async () => {
    const assignments = await assignmentsOf(
      "REMOVE",
      `bus.on("REMOVE", () => { --bookmarkCount.value; });`
    );
    expect(assignments).toEqual([{ field: "bookmarkCount", value: "@ - 1" }]);
  });

  test("`count.value += 2` writes the signal's own field", async () => {
    const assignments = await assignmentsOf(
      "ADD_TWO",
      `bus.on("ADD_TWO", () => { bookmarkCount.value += 2; });`
    );
    expect(assignments).toEqual([{ field: "bookmarkCount", value: "@ + 2" }]);
  });

  test("an object signal's field keeps its own name", async () => {
    const assignments = await assignmentsOf(
      "MINT",
      `bus.on("MINT", () => { session.value.outstanding++; });`
    );
    expect(assignments).toEqual([{ field: "outstanding", value: "@ + 1" }]);
  });

  test("a nested `.value` path is not taken for a signal", async () => {
    const assignments = await assignmentsOf(
      "NESTED",
      `declare const holder: { inner: { value: number } };
bus.on("NESTED", () => { holder.inner.value++; });`
    );
    expect(assignments ?? []).toEqual([]);
  });
});
