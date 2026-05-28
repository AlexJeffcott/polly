// polly#147 — object-literal signal updates with a non-literal RHS used to be
// silently dropped: `extractValue` only handled literals, so a counter like
// `sessions.value = { outstanding: sessions.value.outstanding + 1 }` produced
// no assignment and the generated action was an UNCHANGED stub. The extractor
// now captures any translatable expression initializer as an `EXPR:` marker,
// mirroring how `state.foo += 1` keeps its RHS, so codegen can translate it.

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("HandlerExtractor — object-literal arithmetic RHS (polly#147)", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-147-test-"));
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

  function extract(body: string) {
    fs.writeFileSync(
      path.join(tempDir, "handlers.ts"),
      `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare const bus: {
  on: <T>(type: string, fn: (payload: T) => void) => void;
};

const sessions = $sharedState("sessions", { outstanding: 0 });
const other = $sharedState("other", { count: 0 });

${body}
`
    );
    return new HandlerExtractor(createTsConfig()).extractHandlers();
  }

  test("mint: `{ outstanding: sessions.value.outstanding + 1 }` is captured as an EXPR", () => {
    const result = extract(`
bus.on("MINT", () => {
  sessions.value = { outstanding: sessions.value.outstanding + 1 };
});
`);
    const handler = result.handlers.find((h) => h.messageType === "MINT");
    expect(handler).toBeDefined();
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([
        { field: "sessions_outstanding", value: "EXPR:sessions.value.outstanding + 1" },
      ])
    );
  });

  test("revoke: subtraction RHS is captured", () => {
    const result = extract(`
bus.on("REVOKE", () => {
  sessions.value = { outstanding: sessions.value.outstanding - 1 };
});
`);
    const handler = result.handlers.find((h) => h.messageType === "REVOKE");
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([
        { field: "sessions_outstanding", value: "EXPR:sessions.value.outstanding - 1" },
      ])
    );
  });

  test("spread + arithmetic: the spread is ignored, the arithmetic field captured", () => {
    const result = extract(`
bus.on("MINT_SPREAD", () => {
  sessions.value = { ...sessions.value, outstanding: sessions.value.outstanding + 1 };
});
`);
    const handler = result.handlers.find((h) => h.messageType === "MINT_SPREAD");
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([
        { field: "sessions_outstanding", value: "EXPR:sessions.value.outstanding + 1" },
      ])
    );
  });

  test("plain copy of another field is captured as an EXPR", () => {
    const result = extract(`
bus.on("COPY", () => {
  sessions.value = { outstanding: other.value.count };
});
`);
    const handler = result.handlers.find((h) => h.messageType === "COPY");
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([{ field: "sessions_outstanding", value: "EXPR:other.value.count" }])
    );
  });

  test("literal RHS is still captured as a plain value (unchanged behaviour)", () => {
    const result = extract(`
bus.on("RESET", () => {
  sessions.value = { outstanding: 0 };
});
`);
    const handler = result.handlers.find((h) => h.messageType === "RESET");
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([{ field: "sessions_outstanding", value: 0 }])
    );
  });

  test("payload-parameter RHS still produces a param: marker, not an EXPR", () => {
    const result = extract(`
bus.on<{ n: number }>("SET", (payload) => {
  sessions.value = { outstanding: payload.n };
});
`);
    const handler = result.handlers.find((h) => h.messageType === "SET");
    expect(handler!.assignments).toEqual(
      expect.arrayContaining([{ field: "sessions_outstanding", value: "param:n" }])
    );
    // ...and definitely not doubly-captured as an expression.
    const outstanding = handler!.assignments.filter((a) => a.field === "sessions_outstanding");
    expect(outstanding).toHaveLength(1);
  });
});
