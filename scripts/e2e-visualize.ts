// End-to-end verification for `polly visualize --generate`.
//
// Per CLAUDE.md ("green checks do not prove features work"): unit tests
// hand-wire the analyzer + DSL generator, which can drift silently from
// the path real users hit. This script copies three real example
// projects to a cold tmp dir, runs the polly CLI exactly as a user
// would (`bun cli/polly.ts visualize`), and asserts the resulting
// docs/architecture.dsl contains pinned context and component
// identifiers.
//
// Scope: --generate only. --export wraps Docker and warrants its own
// script.
//
// Examples covered:
//   minimal           — single-package extension, runs at example root
//   elysia-todo-app   — workspace, runs from server/
//   webrtc-p2p-chat   — workspace, runs from server/
//
// On failure the tmp dir is retained and printed so the generated DSL
// can be inspected in place. On success the tmp dir is removed.
//
// Usage:
//   bun scripts/e2e-visualize.ts

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

const REPO = path.resolve(import.meta.dir, "..");
const POLLY_CLI = path.join(REPO, "cli", "polly.ts");
// Use structurizr/structurizr (the consolidated successor); structurizr/cli is
// deprecated and its `validate` command silently no-ops on invalid input.
const STRUCTURIZR_IMAGE = "structurizr/structurizr:latest";
const SKIP_DOCKER = process.env["SKIP_DOCKER"] === "1";

type Outcome = "passed" | "spawn-failed" | "missing-dsl" | "missing-content" | "validate-failed";

type ValidateStatus = "ok" | "failed" | "skipped";

type Case = {
  label: string;
  examplePath: string;
  cwdSubpath: string;
  expectedWorkspace: string;
  expectedContainers: string[];
  expectedComponents: string[];
  minComponents: number;
  expectedExternalSystems?: string[];
  minRelationships?: number;
};

type Result = {
  label: string;
  outcome: Outcome;
  failures: string[];
  elapsedMs: number;
  tmpRoot: string;
  dslPath?: string;
  cliExitCode?: number;
  cliStderrTail?: string;
  validate: ValidateStatus;
};

const cases: Case[] = [
  {
    label: "minimal",
    examplePath: "examples/minimal",
    cwdSubpath: "",
    expectedWorkspace: "Minimal Example",
    expectedContainers: ["background"],
    expectedComponents: ["ping_handler"],
    minComponents: 1,
  },
  {
    label: "elysia-todo-app",
    examplePath: "examples/elysia-todo-app",
    cwdSubpath: "server",
    expectedWorkspace: "server",
    expectedContainers: ["server"],
    expectedComponents: [
      "login_handler",
      "logout_handler",
      "post_auth_login",
      "post_auth_logout",
      "delete_todos_id",
      "patch_todos_id",
      "post_todos",
      "get_todos",
    ],
    minComponents: 8,
    expectedExternalSystems: ["localhost_api"],
    minRelationships: 6,
  },
  {
    label: "webrtc-p2p-chat",
    examplePath: "examples/webrtc-p2p-chat",
    cwdSubpath: "server",
    expectedWorkspace: "server",
    expectedContainers: ["server"],
    expectedComponents: [
      "join_room_handler",
      "leave_room_handler",
      "offer_handler",
      "answer_handler",
      "ice_candidate_handler",
      "ws_open_handler",
      "ws_close_handler",
      "get_stats",
      "get_health",
    ],
    minComponents: 9,
  },
];

let dockerProbe: Promise<boolean> | null = null;
async function dockerAvailable(): Promise<boolean> {
  if (SKIP_DOCKER) return false;
  if (!dockerProbe) {
    dockerProbe = (async () => {
      const proc = Bun.spawn(["docker", "--version"], { stdout: "pipe", stderr: "pipe" });
      return (await proc.exited) === 0;
    })();
  }
  return dockerProbe;
}

async function structurizrValidate(dslPath: string): Promise<{ ok: boolean; output: string }> {
  const dslDir = path.dirname(dslPath);
  const dslName = path.basename(dslPath);
  const proc = Bun.spawn(
    [
      "docker",
      "run",
      "--rm",
      "-v",
      `${dslDir}:/work`,
      STRUCTURIZR_IMAGE,
      "validate",
      "-workspace",
      `/work/${dslName}`,
    ],
    { stdout: "pipe", stderr: "pipe" }
  );
  const exitCode = await proc.exited;
  const stdout = await new Response(proc.stdout).text();
  const stderr = await new Response(proc.stderr).text();
  const combined = `${stdout}${stderr}`;
  // structurizr/structurizr exits 0 even on validation errors; scan for ERROR lines.
  const errorLines = combined
    .split("\n")
    .filter((l) => / ERROR /.test(l))
    .join("\n");
  const ok = exitCode === 0 && errorLines === "";
  return { ok, output: errorLines || combined };
}

function copyExample(src: string, dst: string): void {
  fs.cpSync(src, dst, {
    recursive: true,
    filter: (p) => {
      const base = path.basename(p);
      return base !== "node_modules" && base !== "dist" && base !== "docs";
    },
  });
}

async function runOne(c: Case): Promise<Result> {
  const start = Date.now();
  const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), `e2e-viz-${c.label}-`));
  const exampleCopy = path.join(tmpRoot, path.basename(c.examplePath));
  copyExample(path.join(REPO, c.examplePath), exampleCopy);

  const cwd = c.cwdSubpath ? path.join(exampleCopy, c.cwdSubpath) : exampleCopy;

  const proc = Bun.spawn(["bun", POLLY_CLI, "visualize"], {
    cwd,
    stdout: "pipe",
    stderr: "pipe",
    env: { ...process.env },
  });
  const exitCode = await proc.exited;
  const stderrTail = (await new Response(proc.stderr).text()).slice(-400);

  if (exitCode !== 0) {
    return {
      label: c.label,
      outcome: "spawn-failed",
      failures: [`polly visualize exited ${exitCode}`],
      elapsedMs: Date.now() - start,
      tmpRoot,
      cliExitCode: exitCode,
      cliStderrTail: stderrTail,
      validate: "skipped",
    };
  }

  const dslPath = path.join(cwd, "docs", "architecture.dsl");
  if (!fs.existsSync(dslPath)) {
    return {
      label: c.label,
      outcome: "missing-dsl",
      failures: [`expected ${dslPath}`],
      elapsedMs: Date.now() - start,
      tmpRoot,
      validate: "skipped",
    };
  }

  const dsl = fs.readFileSync(dslPath, "utf8");
  const failures = checkDsl(c, dsl);

  let validate: ValidateStatus = "skipped";
  if (failures.length === 0 && (await dockerAvailable())) {
    const result = await structurizrValidate(dslPath);
    if (result.ok) {
      validate = "ok";
    } else {
      validate = "failed";
      failures.push(`structurizr validate failed:\n${result.output.trim().slice(0, 600)}`);
    }
  }

  let outcome: Outcome = "passed";
  if (failures.length > 0) {
    outcome = validate === "failed" ? "validate-failed" : "missing-content";
  }

  return {
    label: c.label,
    outcome,
    failures,
    elapsedMs: Date.now() - start,
    tmpRoot,
    dslPath,
    validate,
  };
}

function missingDeclarations(dsl: string, kind: string, ids: string[], keyword: string): string[] {
  const out: string[] = [];
  for (const id of ids) {
    // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp — `id` is escapeRe-sanitised; `keyword` is a hardcoded callsite literal.
    const re = new RegExp(`\\b${escapeRe(id)}\\s*=\\s*${keyword}\\b`);
    if (!re.test(dsl)) out.push(`${kind} ${id} not found`);
  }
  return out;
}

function checkDsl(c: Case, dsl: string): string[] {
  const failures: string[] = [];

  if (!dsl.includes(`workspace "${c.expectedWorkspace}"`)) {
    failures.push(`workspace "${c.expectedWorkspace}" not found`);
  }
  if (!/\bmodel\s*\{/.test(dsl)) failures.push("model block not found");
  if (!/\bviews\s*\{/.test(dsl)) failures.push("views block not found");

  failures.push(...missingDeclarations(dsl, "container", c.expectedContainers, "container"));
  failures.push(...missingDeclarations(dsl, "component", c.expectedComponents, "component"));
  failures.push(
    ...missingDeclarations(
      dsl,
      "external softwareSystem",
      c.expectedExternalSystems ?? [],
      "softwareSystem"
    )
  );

  const componentCount = (dsl.match(/=\s*component\b/g) ?? []).length;
  if (componentCount < c.minComponents) {
    failures.push(`expected ≥${c.minComponents} components, got ${componentCount}`);
  }

  if (c.minRelationships !== undefined) {
    const relCount = (dsl.match(/\s->\s/g) ?? []).length;
    if (relCount < c.minRelationships) {
      failures.push(`expected ≥${c.minRelationships} relationships, got ${relCount}`);
    }
  }

  return failures;
}

function escapeRe(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function pad(s: string, n: number): string {
  return s.length >= n ? s : s + " ".repeat(n - s.length);
}

function reportFailure(r: Result): void {
  console.log(`\n  ${r.label} — ${r.outcome}`);
  for (const f of r.failures) console.log(`    - ${f}`);
  if (r.cliStderrTail) {
    console.log(`    stderr tail:`);
    for (const line of r.cliStderrTail.split("\n")) console.log(`      ${line}`);
  }
  console.log(`    tmp:    ${r.tmpRoot}`);
  if (r.dslPath) console.log(`    dsl:    ${r.dslPath}`);
}

async function describeDockerStatus(): Promise<string> {
  if (SKIP_DOCKER) return "SKIP_DOCKER=1 (structurizr validate disabled)";
  if (await dockerAvailable()) return "available (structurizr validate enabled)";
  return "not available (structurizr validate skipped)";
}

async function main(): Promise<void> {
  console.log("E2E: polly visualize --generate\n");
  console.log(`  Repo:      ${REPO}`);
  console.log(`  CLI entry: ${POLLY_CLI}`);
  console.log(`  Docker:    ${await describeDockerStatus()}`);
  console.log();

  const results: Result[] = [];
  for (const c of cases) {
    process.stdout.write(`  ▸ ${pad(c.label, 20)} ... `);
    const r = await runOne(c);
    results.push(r);
    const tag = r.outcome === "passed" ? "PASS" : "FAIL";
    const validateMark =
      r.validate === "ok" ? " [validated]" : r.validate === "failed" ? " [validate ✗]" : "";
    console.log(`${tag}${validateMark}  (${(r.elapsedMs / 1000).toFixed(1)}s)`);
  }

  console.log("\nDetails:");
  for (const r of results) {
    if (r.outcome === "passed") {
      fs.rmSync(r.tmpRoot, { recursive: true, force: true });
    } else {
      reportFailure(r);
    }
  }

  const failed = results.filter((r) => r.outcome !== "passed").length;
  console.log();
  if (failed > 0) {
    console.log(`${failed}/${results.length} failed`);
    process.exit(1);
  }
  console.log(`All ${results.length} passed`);
}

main().catch((err) => {
  console.log(String(err?.stack ?? err));
  process.exit(1);
});
