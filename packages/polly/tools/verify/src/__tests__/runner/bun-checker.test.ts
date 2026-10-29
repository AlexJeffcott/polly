/**
 * The Bun checker (checker/check.ts) on small hand-written specs, one TLC rule
 * per test. Counts were worked out by hand from TLC's rules: initial states
 * count as generated; a successor outside the CONSTRAINT counts as generated,
 * is invariant-checked and is not expanded; depth is the number of BFS levels.
 * Parity with TLC on the generated example specs is
 * scripts/e2e-verify-bun-parity.ts (needs Docker).
 */

import { afterEach, describe, expect, test } from "bun:test";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkSpec } from "../../checker/check";
import { runBunChecker } from "../../runner/bun-engine";

const dirs: string[] = [];

afterEach(() => {
  for (const d of dirs.splice(0)) rmSync(d, { recursive: true, force: true });
});

function spec(body: string, cfg: string): string {
  const dir = mkdtempSync(join(tmpdir(), "polly-bun-checker-"));
  dirs.push(dir);
  writeFileSync(
    join(dir, "M.tla"),
    `---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\n${body}\n====\n`
  );
  writeFileSync(join(dir, "M.cfg"), cfg);
  return dir;
}

const CYCLE = `Init == x = 0
Next == \\/ /\\ x < 3
           /\\ x' = x + 1
        \\/ /\\ x = 3
           /\\ x' = 0
Spec == Init /\\ [][Next]_x
TypeOK == x \\in 0..3`;

describe("Bun checker", () => {
  test("an exhausted model gives TLC's counts", () => {
    const dir = spec(CYCLE, "SPECIFICATION Spec\nINVARIANT TypeOK\n");
    const r = checkSpec({ specDir: dir, moduleName: "M" });
    expect(r.kind).toBe("done");
    if (r.kind !== "done") return;
    // 1 initial + one successor from each of the 4 states.
    expect(r.counts).toEqual({ generated: 5, distinct: 4, depth: 4, initial: 1, leftOnQueue: 0 });
  });

  test("an invariant violation gives the shortest trace", () => {
    const dir = spec(`${CYCLE}\nBelow2 == x < 2`, "SPECIFICATION Spec\nINVARIANT Below2\n");
    const r = checkSpec({ specDir: dir, moduleName: "M" });
    expect(r.kind).toBe("violation");
    if (r.kind !== "violation") return;
    expect(r.what).toBe("invariant");
    expect(r.name).toBe("Below2");
    expect(r.trace).toEqual([
      "State 1: <Initial predicate>",
      "/\\ x = 0",
      "State 2:",
      "/\\ x = 1",
      "State 3:",
      "/\\ x = 2",
    ]);
    expect(r.counts.depth).toBe(3);
  });

  test("a state with no successor is a deadlock, reported with its trace", () => {
    const body = `Init == x = 0
Next == x < 2 /\\ x' = x + 1
Spec == Init /\\ [][Next]_x`;
    const r = checkSpec({ specDir: spec(body, "SPECIFICATION Spec\n"), moduleName: "M" });
    expect(r.kind).toBe("violation");
    if (r.kind !== "violation") return;
    expect(r.what).toBe("deadlock");
    expect(r.trace.filter((l) => l.startsWith("State "))).toHaveLength(3);
    expect(r.trace.at(-1)).toBe("/\\ x = 2");
  });

  test("a successor outside the CONSTRAINT is generated and checked, not stored or expanded", () => {
    const passing = spec(
      `${CYCLE}\nSmall == x <= 1`,
      "SPECIFICATION Spec\nINVARIANT TypeOK\nCONSTRAINT Small\n"
    );
    const r = checkSpec({ specDir: passing, moduleName: "M" });
    expect(r.kind).toBe("done");
    if (r.kind !== "done") return;
    // x = 0, 1 stored; x = 2 generated, outside, not expanded.
    expect(r.counts).toMatchObject({ generated: 3, distinct: 2, depth: 2 });

    const failing = spec(
      `${CYCLE}\nSmall == x <= 1\nNot2 == x # 2`,
      "SPECIFICATION Spec\nINVARIANT Not2\nCONSTRAINT Small\n"
    );
    const v = checkSpec({ specDir: failing, moduleName: "M" });
    expect(v.kind).toBe("violation");
    if (v.kind === "violation") expect(v.name).toBe("Not2");
  });

  test("PROPERTIES are returned, not checked", () => {
    const dir = spec(
      `${CYCLE}\nEventually3 == <>(x = 3)`,
      "SPECIFICATION Spec\nINVARIANT TypeOK\nPROPERTIES\n  Eventually3\n"
    );
    const r = checkSpec({ specDir: dir, moduleName: "M" });
    expect(r.kind).toBe("done");
    if (r.kind === "done") expect(r.properties).toEqual(["Eventually3"]);
  });

  test("a cfg section the checker does not support is unsupported, never a pass", () => {
    const dir = spec(CYCLE, "SPECIFICATION Spec\nSYMMETRY Perms\n");
    const r = checkSpec({ specDir: dir, moduleName: "M" });
    expect(r).toEqual({ kind: "unsupported", reason: "cfg SYMMETRY" });
    expect(runBunChecker(join(dir, "M.tla"), {}).kind).toBe("unsupported");
  });

  test("handler actions are counted at their last conjunct, inside a quantifier too", () => {
    const body = `Init == x = 0
HandleUp(ctx) ==
  /\\ x < 2
  /\\ x' = x + 1
HandleNever(ctx) ==
  /\\ x > 5
  /\\ x' = 0
HandleReset(ctx) ==
  /\\ x = 2
  /\\ x' = 0
Next == \\E c \\in {1, 2} : HandleUp(c) \\/ HandleNever(c) \\/ HandleReset(c)
Spec == Init /\\ [][Next]_x`;
    const r = checkSpec({ specDir: spec(body, "SPECIFICATION Spec\n"), moduleName: "M" });
    expect(r.kind).toBe("done");
    if (r.kind !== "done") return;
    // Each of x = 0, 1 is expanded once, for both values of c.
    expect(r.handlerCounts.get("HandleUp")).toBe(4);
    expect(r.handlerCounts.get("HandleReset")).toBe(2);
    expect(r.handlerCounts.get("HandleNever")).toBe(0);
  });

  test("a run past its timeout reports the states left, not a pass", () => {
    const body = `Init == x = 0
Next == x' = (x + 1) % 100000
Spec == Init /\\ [][Next]_x`;
    const r = checkSpec({
      specDir: spec(body, "SPECIFICATION Spec\n"),
      moduleName: "M",
      timeoutMs: 0,
    });
    expect(r.kind).toBe("timeout");
    if (r.kind !== "timeout") return;
    expect(r.counts.leftOnQueue).toBeGreaterThan(0);
    const tlc = runBunChecker(join(dirs.at(-1) ?? "", "M.tla"), { timeoutMs: 0 });
    expect(tlc.kind === "result" && tlc.result.success).toBe(false);
  });
});
