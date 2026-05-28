// polly#147 — integration test across the documented pipeline
// (analyzeCodebase → generateTLA). A counter updated through an object-literal
// signal write with an arithmetic RHS used to extract no assignment, so the
// generated action was an `UNCHANGED contextStates` stub and the bounded-
// counter ensures could never be satisfied — TLC reported a real-looking
// violation that was really an extractor gap. This proves the two halves
// compose: the EXPR assignment survives extraction AND becomes a real EXCEPT.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { analyzeCodebase } from "../../../../analysis/src/extract/types";
import { generateTLA } from "../../codegen/tla";
import type { VerificationConfig } from "../../types";

function writeProject(dir: string, handlerBody: string): string {
  const tsConfigPath = path.join(dir, "tsconfig.json");
  fs.writeFileSync(
    tsConfigPath,
    JSON.stringify({
      compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
      include: ["*.ts"],
    })
  );
  fs.writeFileSync(path.join(dir, "package.json"), JSON.stringify({ name: "p", version: "0.0.1" }));
  fs.writeFileSync(
    path.join(dir, "handlers.ts"),
    `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare const bus: { on: <T>(type: string, fn: (payload: T) => void) => void };

const sessions = $sharedState("sessions", { outstanding: 0 });

${handlerBody}
`
  );
  return tsConfigPath;
}

describe("polly#147: object-literal arithmetic survives the full pipeline", () => {
  test("a mint counter generates a real EXCEPT, not an UNCHANGED stub", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-147-int-"));
    try {
      const tsConfigPath = writeProject(
        dir,
        `
bus.on("MINT", () => {
  sessions.value = { outstanding: sessions.value.outstanding + 1 };
});
`
      );

      const analysis = await analyzeCodebase({ tsConfigPath });
      const config: VerificationConfig = {
        state: { sessions: { outstanding: { min: 0, max: 2 } } },
        messages: { maxInFlight: 1, maxTabs: 1 },
        onBuild: "warn",
        onRelease: "error",
      };

      const { spec } = await generateTLA(config, analysis);

      // The handler action must EXCEPT-update the counter with arithmetic...
      expect(spec).toContain(
        "![ctx].sessions_outstanding = contextStates[ctx].sessions_outstanding + 1"
      );

      // ...and must NOT be the dropped-assignment stub.
      const action = spec.slice(spec.indexOf("HandleMint(ctx) =="));
      const nextHandler = action.indexOf("\n\n");
      expect(action.slice(0, nextHandler)).not.toContain("UNCHANGED contextStates");
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  });
});
