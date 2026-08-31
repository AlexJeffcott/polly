// polly#169 / polly#170 — the two halves must compose across the documented
// pipeline (analyzeCodebase → generateTLA), not just in the extractor.
//
// #169: an alias emitted `state.unsyncedChanges`, which the codegen's `state.`
// rule rewrote to `contextStates[ctx].unsyncedChanges` — a member the record
// does not carry. TLC aborted mid-run with `unexpected exception`, a message
// that points at nothing. Under any other alias name the identifier reached
// SANY unbound.
//
// #170: a ternary was dropped, so the action left the field UNCHANGED and every
// property over it held vacuously.

import { describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { analyzeCodebase } from "../../../../analysis/src/extract/types";
import { generateTLA } from "../../codegen/tla";
import { DockerRunner } from "../../runner/docker";
import { SANYRunner } from "../../runner/sany";
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

const offlineQueue = $sharedState("offlineQueue", {
  unsyncedChanges: 0,
  syncState: "synced",
});

${handlerBody}
`
  );
  return tsConfigPath;
}

const config: VerificationConfig = {
  state: {
    offlineQueue: {
      unsyncedChanges: { min: 0, max: 3 },
      syncState: { type: "enum", values: ["synced", "pending"] },
    },
  },
  messages: { maxInFlight: 1, maxTabs: 1 },
  onBuild: "warn",
  onRelease: "error",
};

async function generatedFor(handlerBody: string): Promise<{ spec: string; cfg: string }> {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-169-170-int-"));
  try {
    const tsConfigPath = writeProject(dir, handlerBody);
    const analysis = await analyzeCodebase({ tsConfigPath });
    const { spec, cfg } = await generateTLA(config, analysis);
    return { spec, cfg };
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

async function specFor(handlerBody: string): Promise<string> {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-169-170-int-"));
  try {
    const tsConfigPath = writeProject(dir, handlerBody);
    const analysis = await analyzeCodebase({ tsConfigPath });
    const { spec } = await generateTLA(config, analysis);
    return spec;
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

/** The body of one handler action, up to the next blank line. */
function actionBody(spec: string, name: string): string {
  const start = spec.indexOf(`${name}(ctx) ==`);
  expect(start).toBeGreaterThan(-1);
  const rest = spec.slice(start);
  const end = rest.indexOf("\n\n");
  return end === -1 ? rest : rest.slice(0, end);
}

describe("polly#169: an aliased signal read resolves to the right record member", () => {
  test("an alias named `state` does not collapse onto the framework `state.` form", async () => {
    const spec = await specFor(`
bus.on("QUEUE_OP", () => {
  const state = offlineQueue.value;
  offlineQueue.value = {
    ...state,
    unsyncedChanges: state.unsyncedChanges + 1,
  };
});
`);

    expect(spec).toContain(
      "![ctx].offlineQueue_unsyncedChanges = contextStates[ctx].offlineQueue_unsyncedChanges + 1"
    );

    // The defect: a bare `unsyncedChanges` member that does not exist.
    expect(spec).not.toContain("contextStates[ctx].unsyncedChanges");
  });

  test("an alias under another name leaves no free identifier in the spec", async () => {
    const spec = await specFor(`
bus.on("QUEUE_OP", () => {
  const q = offlineQueue.value;
  offlineQueue.value = { ...q, unsyncedChanges: q.unsyncedChanges + 1 };
});
`);

    expect(spec).toContain(
      "![ctx].offlineQueue_unsyncedChanges = contextStates[ctx].offlineQueue_unsyncedChanges + 1"
    );
    // `q` reaching SANY unbound is the second failure shape in polly#169.
    expect(spec).not.toMatch(/\bq\.unsyncedChanges\b/);
  });
});

describe("polly#170: a single ternary becomes a real transition", () => {
  test("the action moves syncState instead of leaving it UNCHANGED", async () => {
    const spec = await specFor(`
bus.on("MARK_PENDING", () => {
  const state = offlineQueue.value;
  offlineQueue.value = {
    ...state,
    syncState: state.syncState === "synced" ? "pending" : state.syncState,
  };
});
`);

    const body = actionBody(spec, "HandleMarkPending");

    // Translated to a TLA+ conditional, not dropped.
    expect(body).toContain("IF");
    expect(body).toContain("THEN");
    expect(body).toContain("ELSE");
    expect(body).toContain("offlineQueue_syncState");

    // The silent-stub shape polly#147 documented and polly#170 reproduced.
    expect(body).not.toContain("UNCHANGED contextStates");

    // TLA+ string literals are double-quoted. A surviving single-quoted literal
    // is the corruption the quote-conversion pass produced on a ternary; the
    // lone `'` in `contextStates'` is the prime operator and is expected.
    expect(body).not.toMatch(/'(synced|pending)/);
    expect(body).toContain('"synced"');
    expect(body).toContain('"pending"');
  });
});

/**
 * polly#170's core risk is not a dropped assignment but an emitted one that
 * SANY rejects: `translateTernary` is a regex, and before this fix a
 * parenthesized ternary produced `IF (a THEN 1 ELSE 0)` — unbalanced
 * parentheses. Asserting on the generated text cannot catch that; only the
 * parser can. Runs in the `verify` tier, which already requires Docker.
 */
function dockerAvailable(): boolean {
  if (process.env["SKIP_DOCKER"] === "1") return false;
  try {
    return spawnSync("docker", ["info"], { timeout: 10_000, stdio: "ignore" }).status === 0;
  } catch {
    return false;
  }
}

describe.skipIf(!dockerAvailable())("the generated spec parses", () => {
  test("SANY accepts a spec carrying both an alias-resolved counter and a ternary", async () => {
    const { spec, cfg } = await generatedFor(`
bus.on("QUEUE_OP", () => {
  const state = offlineQueue.value;
  offlineQueue.value = { ...state, unsyncedChanges: state.unsyncedChanges + 1 };
});
bus.on("MARK_PENDING", () => {
  const state = offlineQueue.value;
  offlineQueue.value = {
    ...state,
    syncState: state.syncState === "synced" ? "pending" : state.syncState,
  };
});
`);

    const specDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-169-170-sany-"));
    try {
      fs.writeFileSync(path.join(specDir, "UserApp.tla"), spec);
      fs.writeFileSync(path.join(specDir, "UserApp.cfg"), cfg);
      fs.copyFileSync(
        path.join(import.meta.dir, "../../../specs/tla/MessageRouter.tla"),
        path.join(specDir, "MessageRouter.tla")
      );

      const result = await new SANYRunner(new DockerRunner()).validateSpec(
        path.join(specDir, "UserApp.tla")
      );

      expect(result.errors.map((e) => e.message)).toEqual([]);
      expect(result.valid).toBe(true);
    } finally {
      fs.rmSync(specDir, { recursive: true, force: true });
    }
  }, 90_000);
});
