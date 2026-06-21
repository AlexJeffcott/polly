// polly#163: off-surface mutator detection — verified-state writes that fall
// outside every function the extractor models as a handler (the non-dispatched
// register() shape #160).

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

const STATE_PRELUDE = `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}
export const session = $sharedState('session', { authenticated: false, canSend: false }, { verify: true });
`;

describe("HandlerExtractor - off-surface mutators (polly#163)", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-offsurface-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) fs.rmSync(tempDir, { recursive: true });
  });

  function run(files: Record<string, string>): ReturnType<HandlerExtractor["extractHandlers"]> {
    fs.writeFileSync(
      path.join(tempDir, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
        include: ["**/*.ts"],
      })
    );
    for (const [rel, content] of Object.entries(files)) {
      const full = path.join(tempDir, rel);
      fs.mkdirSync(path.dirname(full), { recursive: true });
      fs.writeFileSync(full, content);
    }
    return new HandlerExtractor(path.join(tempDir, "tsconfig.json")).extractHandlers();
  }

  test("reports a write inside a class method", () => {
    const result = run({
      "app.ts": `${STATE_PRELUDE}
class RecoveryFlow {
  register() {
    session.value.canSend = true;
  }
}
new RecoveryFlow().register();
`,
    });
    expect(result.offSurfaceMutations).toHaveLength(1);
    expect(result.offSurfaceMutations[0]).toMatchObject({
      field: "session_canSend",
      signalVariable: "session",
      functionName: "RecoveryFlow.register",
    });
  });

  test("reports a write inside a non-exported function", () => {
    const result = run({
      "app.ts": `${STATE_PRELUDE}
function grant() {
  session.value.canSend = true;
}
grant();
`,
    });
    expect(result.offSurfaceMutations.map((m) => m.functionName)).toEqual(["grant"]);
    expect(result.offSurfaceMutations[0]?.field).toBe("session_canSend");
  });

  test("reports a write at module top level as <module>", () => {
    const result = run({
      "app.ts": `${STATE_PRELUDE}
session.value.canSend = true;
`,
    });
    expect(result.offSurfaceMutations.map((m) => m.functionName)).toEqual(["<module>"]);
  });

  test("does NOT report a write inside an exported function (lifted by Issue #27)", () => {
    const result = run({
      "app.ts": `${STATE_PRELUDE}
export function authenticate() {
  session.value.authenticated = true;
  session.value.canSend = true;
}
`,
    });
    // The exported mutator is modelled as a synthetic handler — on-surface.
    expect(result.offSurfaceMutations).toEqual([]);
    expect(result.handlers.some((h) => h.messageType === "Authenticate")).toBe(true);
  });

  test("a whole-state replacement reports one finding per object-literal key", () => {
    const result = run({
      "app.ts": `${STATE_PRELUDE}
class Reset {
  run() {
    session.value = { authenticated: false, canSend: false };
  }
}
new Reset().run();
`,
    });
    expect(result.offSurfaceMutations.map((m) => m.field).sort()).toEqual([
      "session_authenticated",
      "session_canSend",
    ]);
    expect(new Set(result.offSurfaceMutations.map((m) => m.functionName))).toEqual(
      new Set(["Reset.run"])
    );
  });

  test("excludes test files (fixtures seed state by design)", () => {
    const result = run({
      "app.ts": STATE_PRELUDE,
      "app.test.ts": `import { session } from "./app";
session.value.canSend = true;
`,
    });
    expect(result.offSurfaceMutations).toEqual([]);
  });

  test("reports writes only for state-signal factories, not arbitrary .value writes", () => {
    const result = run({
      "app.ts": `${STATE_PRELUDE}
const plain = { value: 0 };
function touch() {
  plain.value = 5;
  session.value.canSend = true;
}
touch();
`,
    });
    // `plain` is not a state signal; only the session write is off-surface.
    expect(result.offSurfaceMutations.map((m) => m.signalVariable)).toEqual(["session"]);
  });
});
