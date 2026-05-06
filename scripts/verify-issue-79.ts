// End-to-end verification for issue #79.
//
// Issue #78 added per-subsystem bounds.maxInFlight so payload-free
// subsystems can run at higher exploration depth than payload-carrying
// ones. The compositional decomposition is sound on writes —
// checkNonInterference rejects any handler that writes to a field
// owned by another subsystem — but it has been silently unsound on
// reads. A handler in subsystem A whose requires() reads state owned
// by subsystem B will silently never have its postcondition evaluated
// under the compositional verification of A alone: none of B's
// handlers run during A's pass, so the pre-state A's handler waits
// for is never produced. From inside A's verification this looks
// identical to a handler that is unreachable, and TLC reports A as
// PASS without ever firing the property the user wrote.
//
// This script pins the new checkPreconditionLocality analyzer that
// closes the gap. It synthesises two fixtures that share a structure
// — three handlers across two subsystems — and differ only in whether
// one handler's requires() crosses a subsystem boundary.
//
// Fixture A (clean):
//   subsystems
//     auth       state user.loggedIn       handlers Login
//     connection state connectionState.phase handlers Connect, Disconnect
//   Disconnect requires state.connectionState.phase === 'connected'
//   → all reads local; no warning expected.
//
// Fixture B (violating):
//   same subsystems and handlers, but Disconnect now also requires
//   state.user.loggedIn === true — a field owned by `auth`.
//   → checkPreconditionLocality must flag exactly one violation:
//     handler Disconnect (connection) reads user.loggedIn (auth).
//
// Expected results:
//   clean      → valid=true,  violations.length=0
//   violating  → valid=false, violations.length=1, ownedBy=auth
//
// The script exits 0 only when both fixtures match their expected
// outcome. No Docker or TLC required — the analyzer is static.

import {
  checkPreconditionLocality,
  type PreconditionLocalityResult,
} from "../tools/verify/src/analysis/precondition-locality";
import type { MessageHandler, VerificationCondition } from "../tools/verify/src/types";

function makeHandler(messageType: string, writes: string[], requires: string[]): MessageHandler {
  const preconditions: VerificationCondition[] = requires.map((expression, i) => ({
    expression,
    location: { line: i + 1, column: 1 },
  }));
  return {
    messageType,
    node: "background",
    assignments: writes.map((field) => ({ field, value: "true" })),
    preconditions,
    postconditions: [],
    location: { file: "scripts/verify-issue-79.ts", line: 1 },
  };
}

const subsystems = {
  auth: {
    state: ["user.loggedIn"],
    handlers: ["Login"],
  },
  connection: {
    state: ["connectionState.phase"],
    handlers: ["Connect", "Disconnect"],
  },
};

function buildClean(): MessageHandler[] {
  return [
    makeHandler("Login", ["user.loggedIn"], ["state.user.loggedIn === false"]),
    makeHandler("Connect", ["connectionState.phase"], []),
    makeHandler(
      "Disconnect",
      ["connectionState.phase"],
      ["state.connectionState.phase === 'connected'"]
    ),
  ];
}

function buildViolating(): MessageHandler[] {
  return [
    makeHandler("Login", ["user.loggedIn"], ["state.user.loggedIn === false"]),
    makeHandler("Connect", ["connectionState.phase"], []),
    makeHandler(
      "Disconnect",
      ["connectionState.phase"],
      [
        // Local read OK
        "state.connectionState.phase === 'connected'",
        // Cross-subsystem read: this is the bug.
        "state.user.loggedIn === true",
      ]
    ),
  ];
}

type Case = {
  label: string;
  handlers: MessageHandler[];
  expected: { valid: boolean; violations: number; ownedBy?: string };
  rationale: string;
};

function run(c: Case): { ok: boolean; result: PreconditionLocalityResult } {
  const result = checkPreconditionLocality(subsystems, c.handlers);
  let ok = result.valid === c.expected.valid;
  if (ok) ok = result.violations.length === c.expected.violations;
  if (ok && c.expected.ownedBy) {
    ok = result.violations.some((v) => v.ownedBy === c.expected.ownedBy);
  }
  return { ok, result };
}

function main(): void {
  console.log("Issue #79 e2e: cross-subsystem requires() reads are flagged\n");

  const cases: Case[] = [
    {
      label: "clean",
      handlers: buildClean(),
      expected: { valid: true, violations: 0 },
      rationale: "all requires() reads stay inside their subsystem",
    },
    {
      label: "violating",
      handlers: buildViolating(),
      expected: { valid: false, violations: 1, ownedBy: "auth" },
      rationale: "Disconnect (connection) requires user.loggedIn (auth)",
    },
  ];

  let allOk = true;
  for (const c of cases) {
    const { ok, result } = run(c);
    if (!ok) allOk = false;
    const mark = ok ? "OK" : "MISMATCH";
    const summary = `valid=${result.valid} violations=${result.violations.length}`;
    console.log(`▸ ${c.label.padEnd(12)} ${mark}  ${summary.padEnd(28)}  — ${c.rationale}`);
    if (!ok) {
      for (const v of result.violations) {
        console.log(
          `   ↳ ${v.handler} (${v.subsystem}) reads ${v.readsFrom} owned by ${v.ownedBy}`
        );
        console.log(`      ${v.expression}`);
      }
    }
  }

  console.log();
  if (allOk) {
    console.log(
      "Issue #79 verification PASSED — checkPreconditionLocality flags cross-subsystem reads."
    );
    return;
  }
  console.log("Issue #79 verification FAILED.");
  process.exit(1);
}

main();
