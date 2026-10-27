// End-to-end verification for `polly visualize --generate`.
//
// Per CLAUDE.md ("green checks do not prove features work"): unit tests
// hand-wire the analyzer + DSL generator, which can drift silently from
// the path real users hit. This script copies every example project
// to a cold tmp dir, runs the polly CLI exactly as a user would
// (`bun cli/polly.ts visualize`), and asserts the resulting
// docs/architecture.dsl contains pinned context and component
// identifiers.
//
// Scope: `generate`, with and without `--snapshot`. `--export` wraps
// Docker and warrants its own script.
//
// Examples covered: every examples/* project with a package.json, run at
// its root, and each workspace example also from server/. A guard fails
// the run when an example has no case, so a new example cannot go
// unvalidated (four invalid DSLs once went unnoticed that way). Plus
// mesh-overlay (polly#127: `generate --snapshot` overlays a captured
// MeshClientPeerStateSnapshot).
//
// Every generated DSL is validated by Structurizr when Docker is
// available. Without Docker, cheap static checks still catch the defects
// Structurizr reported before: an element declared twice in a container,
// a repeated relationship, an edge from an undeclared container, a view
// key outside [A-Za-z0-9_-] or used twice. Every case also asserts that no
// container description is a comment delimiter (`/**`), and that no
// package of the example's own workspace is listed as an external
// integration.
//
// Then the failure paths: generate with no project, export with no DSL,
// serve with no site, a bad --snapshot. Each must exit non-zero AND say
// why on stderr; they used to exit 1 with no output at all.
//
// On failure the tmp dir is retained and printed so the generated DSL
// can be inspected in place. On success the tmp dir is removed.
//
// Usage:
//   bun scripts/e2e-visualize.ts
//   POLLY_E2E_VIZ_DSL_DIR=<dir> bun scripts/e2e-visualize.ts   # also keep each DSL

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { stripVTControlCharacters } from "node:util";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { STRUCTURIZR_IMAGE } from "../tools/visualize/src/runner/export";

export const capability = "visualize.generate" as const;

// This script lives in packages/polly/scripts. The polly CLI is in the
// package; the example projects live at the monorepo root — the two are
// not the same directory since the monorepo restructure.
const PACKAGE_DIR = path.resolve(import.meta.dir, "..");
const REPO_ROOT = path.resolve(import.meta.dir, "..", "..", "..");
const POLLY_CLI = path.join(PACKAGE_DIR, "cli", "polly.ts");
// The visualize CLI itself: the signal cases signal it directly, as the
// relay in cli/polly.ts would.
const VISUALIZE_CLI = path.join(PACKAGE_DIR, "tools", "visualize", "src", "cli.ts");
const WORKSPACE_TSCONFIG = "tsconfig.polly-visualize.json";
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
  /** polly#127: snapshot file (relative to the run cwd) passed via
   * `generate --snapshot`. When set, the DSL is checked for the runtime
   * mesh overlay. */
  snapshot?: string;
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
    expectedWorkspace: "elysia-todo-app-server",
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
    // No external systems: the `localhost_api` this case used to expect was
    // api.test.ts fetching the example's own server, which is not an
    // integration. Integration analysis skips test files now.
    minRelationships: 5,
  },
  {
    // Run from the workspace root, which has a package.json and client/ +
    // server/ packages but no tsconfig.json; generate used to exit 1 here
    // with no output.
    label: "elysia-todo-app-root",
    examplePath: "examples/elysia-todo-app",
    cwdSubpath: "",
    expectedWorkspace: "elysia-todo-app-example",
    expectedContainers: ["server", "client"],
    expectedComponents: [
      "login_handler",
      "logout_handler",
      "post_auth_login",
      "post_auth_logout",
      "delete_todos_id",
      "patch_todos_id",
      "post_todos",
      "get_todos",
      "todos_fetchstart_handler",
      "get_client_js",
    ],
    minComponents: 13,
    minRelationships: 5,
  },
  {
    label: "webrtc-p2p-chat",
    examplePath: "examples/webrtc-p2p-chat",
    cwdSubpath: "server",
    expectedWorkspace: "webrtc-p2p-chat-server",
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
  {
    label: "webrtc-p2p-chat-root",
    examplePath: "examples/webrtc-p2p-chat",
    cwdSubpath: "",
    expectedWorkspace: "webrtc-p2p-chat-example",
    expectedContainers: ["client", "server"],
    expectedComponents: ["offer_handler", "join_room_handler"],
    minComponents: 9,
    // client -> server message flows; each (ends, label) once.
    minRelationships: 5,
  },
  {
    label: "blob-share",
    examplePath: "examples/blob-share",
    cwdSubpath: "",
    expectedWorkspace: "blob-share-example",
    expectedContainers: ["client", "server"],
    expectedComponents: [],
    minComponents: 1,
  },
  {
    label: "blob-share-server",
    examplePath: "examples/blob-share",
    cwdSubpath: "server",
    expectedWorkspace: "blob-share-server",
    expectedContainers: ["server"],
    expectedComponents: [],
    minComponents: 1,
  },
  {
    // GET_SETTINGS once was declared in both the query and command groups;
    // the popup and options pages live under src/.
    label: "full-featured",
    examplePath: "examples/full-featured",
    cwdSubpath: "",
    expectedWorkspace: "Full-Featured Example",
    expectedContainers: ["background", "popup", "options"],
    expectedComponents: ["get_settings_handler", "settings_update_handler"],
    minComponents: 10,
    minRelationships: 5,
  },
  {
    label: "mesh-large-initial-sync",
    examplePath: "examples/mesh-large-initial-sync",
    cwdSubpath: "",
    expectedWorkspace: "mesh-large-initial-sync-example",
    expectedContainers: ["server"],
    expectedComponents: [],
    minComponents: 0,
  },
  {
    label: "mesh-large-initial-sync-turn",
    examplePath: "examples/mesh-large-initial-sync-turn",
    cwdSubpath: "",
    expectedWorkspace: "mesh-large-initial-sync-turn-example",
    expectedContainers: ["server"],
    expectedComponents: [],
    minComponents: 0,
  },
  {
    label: "mesh-recovery-pair",
    examplePath: "examples/mesh-recovery-pair",
    cwdSubpath: "",
    expectedWorkspace: "mesh-recovery-pair-example",
    expectedContainers: ["server"],
    expectedComponents: [],
    minComponents: 0,
  },
  {
    label: "showcase",
    examplePath: "examples/showcase",
    cwdSubpath: "",
    expectedWorkspace: "showcase-example",
    expectedContainers: ["main"],
    expectedComponents: [],
    minComponents: 0,
  },
  {
    label: "team-task-manager",
    examplePath: "examples/team-task-manager",
    cwdSubpath: "",
    expectedWorkspace: "team-task-manager",
    expectedContainers: ["client", "server"],
    expectedComponents: [],
    minComponents: 10,
  },
  {
    label: "team-task-manager-server",
    examplePath: "examples/team-task-manager",
    cwdSubpath: "server",
    expectedWorkspace: "team-task-manager-server",
    expectedContainers: ["server"],
    expectedComponents: [],
    minComponents: 5,
  },
  {
    // Its BDD steps send messages too; those are not flows (they once
    // produced edges from a nonexistent `extension.unknown`).
    label: "todo-list",
    examplePath: "examples/todo-list",
    cwdSubpath: "",
    expectedWorkspace: "Todo List Example",
    expectedContainers: ["background", "popup"],
    expectedComponents: ["user_login_handler", "todo_add_handler"],
    minComponents: 6,
    minRelationships: 6,
  },
  {
    // The only case with detected handler relationships, so the only one
    // that emits automatic flow views. Their steps named components by bare
    // id, which `!identifiers hierarchical` rejects; no example caught it.
    label: "cross-file-handlers",
    examplePath: "packages/polly/tools/visualize/src/__tests__/fixtures/cross-file-handlers",
    cwdSubpath: "",
    expectedWorkspace: "Unknown Project",
    expectedContainers: ["server"],
    expectedComponents: ["message_handler", "query_handler", "command_handler", "user_service"],
    minComponents: 7,
    minRelationships: 4,
  },
  {
    // polly#127: the mesh-app fixture declares two $meshState documents;
    // its committed snapshot.json overlays runtime peers and
    // sync-state-coloured edges onto them through the real CLI.
    label: "mesh-overlay",
    examplePath: "packages/polly/tools/visualize/src/__tests__/fixtures/mesh-app",
    cwdSubpath: "",
    expectedWorkspace: "test-mesh-app",
    expectedContainers: ["server", "mesh_doc_chat_rooms", "mesh_doc_chat_presence"],
    expectedComponents: [],
    minComponents: 0,
    snapshot: "snapshot.json",
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
  copyExample(path.join(REPO_ROOT, c.examplePath), exampleCopy);

  const cwd = c.cwdSubpath ? path.join(exampleCopy, c.cwdSubpath) : exampleCopy;

  const cliArgs = c.snapshot ? ["visualize", "generate", "--snapshot", c.snapshot] : ["visualize"];
  const proc = Bun.spawn(["bun", POLLY_CLI, ...cliArgs], {
    cwd,
    stdout: "pipe",
    stderr: "pipe",
    env: { ...process.env },
  });
  const [exitCode, stdout, stderr] = await Promise.all([
    proc.exited,
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  const stderrTail = stderr.slice(-400);

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
  // POLLY_E2E_VIZ_DSL_DIR=<dir> keeps a copy of each case's DSL as
  // <dir>/<label>.dsl, so two runs (before/after a change) can be diffed.
  const keepDir = process.env["POLLY_E2E_VIZ_DSL_DIR"];
  if (keepDir) {
    fs.mkdirSync(keepDir, { recursive: true });
    fs.writeFileSync(path.join(keepDir, `${c.label}.dsl`), dsl);
  }
  const failures = checkDsl(c, dsl);
  failures.push(...checkStructure(dsl));
  failures.push(...checkIntegrations(stdout, workspacePackageNames(exampleCopy)));
  // A workspace root is analysed through a tsconfig generate writes and
  // must remove again.
  const leftover = path.join(cwd, WORKSPACE_TSCONFIG);
  if (fs.existsSync(leftover)) failures.push(`generate left ${leftover} behind`);

  // Validate even when a content check failed: Structurizr's own verdict
  // belongs in the report either way.
  let validate: ValidateStatus = "skipped";
  if (await dockerAvailable()) {
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

  // A software system with no containers draws as an empty box: the project
  // detector found no entry point (showcase and both mesh-large-initial-sync
  // examples, up to 0.97.1).
  if (!/=\s*container\b/.test(dsl)) failures.push("no container declared");
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

  if (c.snapshot) failures.push(...checkOverlay(dsl));

  return failures;
}

const VIEW_KEY = /^[A-Za-z0-9_-]+$/;
const VIEW_LINE = /^\s+(?:systemContext|container|component|dynamic|deployment)\s+\S+\s+"([^"]*)"/;
const CONTAINER_LINE = /^ {6}([A-Za-z0-9_-]+) = container "[^"]*" "([^"]*)"/;
const ELEMENT_LINE = /^\s+([A-Za-z0-9_-]+) = (?:component|container|person|softwareSystem)\b/;
const RELATIONSHIP_LINE = /^\s+(\S+) -> (\S+) "/;

/**
 * Checks a Structurizr parse would fail, made without Docker: what
 * `structurizr validate` reported for the examples before.
 */
function checkStructure(dsl: string): string[] {
  const lines = dsl.split("\n");
  const viewsAt = lines.findIndex((line) => /^ {2}views \{/.test(line));
  const model = viewsAt === -1 ? lines : lines.slice(0, viewsAt);
  const views = viewsAt === -1 ? [] : lines.slice(viewsAt);
  return [
    ...checkContainerDescriptions(model),
    ...checkDuplicateElements(model),
    ...checkRepeatedRelationships(model),
    ...checkEdgeEnds(lines, declaredContainers(model)),
    ...checkViewKeys(views),
  ];
}

function declaredContainers(model: string[]): Set<string> {
  const ids = model.map((line) => CONTAINER_LINE.exec(line)?.[1]);
  return new Set(ids.filter((id) => id !== undefined));
}

/** A JSDoc opener or `//` captured instead of the comment's text. */
function checkContainerDescriptions(model: string[]): string[] {
  const failures: string[] = [];
  for (const line of model) {
    const [, id, description = ""] = CONTAINER_LINE.exec(line) ?? [];
    if (id && /^\s*(?:\/\*|\*\/|\/\/)/.test(description)) {
      failures.push(`container ${id} has a comment delimiter as description: "${description}"`);
    }
  }
  return failures;
}

/**
 * Identifiers are hierarchical: a duplicate is one declared twice inside one
 * container (or twice at the top level).
 */
function checkDuplicateElements(model: string[]): string[] {
  const failures: string[] = [];
  const declared = new Map<string, Set<string>>();
  let parent = "";
  for (const line of model) {
    if (/^ {4}\S/.test(line)) parent = "";
    const container = CONTAINER_LINE.exec(line)?.[1];
    const id = ELEMENT_LINE.exec(line)?.[1];
    if (!id) continue;
    const scope = container ? "extension" : parent;
    if (container) parent = container;
    const ids = declared.get(scope) ?? new Set<string>();
    if (ids.has(id)) failures.push(`element ${id} declared twice in ${scope || "model"}`);
    declared.set(scope, ids.add(id));
  }
  return failures;
}

function checkRepeatedRelationships(model: string[]): string[] {
  const seen = new Set<string>();
  const failures: string[] = [];
  for (const line of model) {
    if (!RELATIONSHIP_LINE.test(line)) continue;
    const rel = line.trim();
    if (seen.has(rel)) failures.push(`relationship repeated: ${rel}`);
    seen.add(rel);
  }
  return failures;
}

/** An `extension.<id>` edge end must be a declared container (not `unknown`). */
function checkEdgeEnds(lines: string[], containers: Set<string>): string[] {
  const failures: string[] = [];
  for (const line of lines) {
    const [, from, to] = RELATIONSHIP_LINE.exec(line) ?? [];
    for (const end of [from, to]) {
      const id = end?.match(/^extension\.([A-Za-z0-9_-]+)$/)?.[1];
      if (id && !containers.has(id)) {
        failures.push(`edge to or from undeclared ${end}: ${line.trim()}`);
      }
    }
  }
  return failures;
}

function checkViewKeys(views: string[]): string[] {
  const failures: string[] = [];
  const keys = new Set<string>();
  for (const line of views) {
    const key = VIEW_LINE.exec(line)?.[1];
    if (key === undefined) continue;
    if (!VIEW_KEY.test(key))
      failures.push(`view key "${key}" has characters outside [A-Za-z0-9_-]`);
    if (keys.has(key)) failures.push(`view key "${key}" used twice`);
    keys.add(key);
  }
  return failures;
}

/** Names of the example's own packages: the root package.json and each child package. */
function workspacePackageNames(exampleRoot: string): string[] {
  const names: string[] = [];
  const dirs = [
    exampleRoot,
    ...fs
      .readdirSync(exampleRoot, { withFileTypes: true })
      .filter((e) => e.isDirectory())
      .map((e) => path.join(exampleRoot, e.name)),
  ];
  for (const dir of dirs) {
    const pkgPath = path.join(dir, "package.json");
    if (!fs.existsSync(pkgPath)) continue;
    const pkg: unknown = JSON.parse(fs.readFileSync(pkgPath, "utf8"));
    const name = pkg && typeof pkg === "object" && "name" in pkg ? pkg.name : undefined;
    if (typeof name === "string") names.push(name);
  }
  return names;
}

/**
 * The integrations generate lists ("• name (type)" under "External
 * Integrations:") must not include a package of the example's own
 * workspace: the client importing the server's types is not a dependency.
 */
function checkIntegrations(stdout: string, ownPackages: string[]): string[] {
  const plain = stripVTControlCharacters(stdout);
  const section =
    plain.split("External Integrations:")[1]?.split("Generating Structurizr DSL")[0] ?? "";
  const listed = [...section.matchAll(/•\s+(\S+)\s+\(/g)].map((m) => m[1]);
  return listed
    .filter((name) => name !== undefined && ownPackages.includes(name))
    .map((name) => `workspace package ${name} listed as an external integration`);
}

/**
 * Every example must be generated: at its root, and from server/ when it
 * is a workspace with a server package.
 */
function checkCoverage(): string[] {
  const covered = new Set(cases.map((c) => path.join(c.examplePath, c.cwdSubpath)));
  const failures: string[] = [];
  const examplesDir = path.join(REPO_ROOT, "examples");
  for (const entry of fs.readdirSync(examplesDir, { withFileTypes: true })) {
    if (!entry.isDirectory()) continue;
    const rel = path.join("examples", entry.name);
    if (!fs.existsSync(path.join(examplesDir, entry.name, "package.json"))) continue;
    if (!covered.has(rel)) failures.push(`${rel} has no case`);
    const server = path.join(rel, "server");
    if (fs.existsSync(path.join(REPO_ROOT, server, "package.json")) && !covered.has(server)) {
      failures.push(`${server} has no case`);
    }
  }
  return failures;
}

/** Log the every-example-has-a-case guard; return its failures. */
function reportCoverage(ctx: TierContext): string[] {
  const failures = checkCoverage();
  ctx.log(`  ▸ ${pad("every example has a case", 28)} ${failures.length === 0 ? "PASS" : "FAIL"}`);
  for (const f of failures) ctx.log(`    - ${f}`);
  return failures;
}

/** Run `fn` over `items` with at most `limit` in flight; results keep input order. */
async function mapPool<T, R>(items: T[], limit: number, fn: (item: T) => Promise<R>): Promise<R[]> {
  const results: R[] = new Array(items.length);
  let next = 0;
  const worker = async () => {
    while (next < items.length) {
      const index = next++;
      const item = items[index];
      if (item !== undefined) results[index] = await fn(item);
    }
  };
  await Promise.all(Array.from({ length: Math.min(limit, items.length) }, worker));
  return results;
}

/**
 * polly#127: assert the runtime mesh overlay reached the DSL — a peer
 * `person` node, status-coloured edges into the static mesh documents,
 * a snapshot-only node, and the `sync:*` relationship styles.
 */
function checkOverlay(dsl: string): string[] {
  const failures: string[] = [];

  if (!dsl.includes('person "peer-aa11"')) {
    failures.push("overlay peer node peer-aa11 not found");
  }
  if (!dsl.includes('tags "Local Mesh Peer"')) {
    failures.push("local peer is not tagged");
  }
  for (const tag of ["sync:has", "sync:wants", "sync:unavailable", "sync:unknown"]) {
    if (!dsl.includes(`tags "${tag}"`)) failures.push(`overlay edge tag ${tag} not found`);
    if (!dsl.includes(`relationship "${tag}"`)) {
      failures.push(`overlay relationship style ${tag} not found`);
    }
  }
  if (!/->\s*extension\.mesh_doc_chat_rooms\b/.test(dsl)) {
    failures.push("overlay edge into mesh_doc_chat_rooms not found");
  }
  if (!dsl.includes('tags "Snapshot Document"')) {
    failures.push("snapshot-only document node not found");
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

type FailureCase = {
  label: string;
  args: string[];
  /** Phrase stderr must contain: the specific reason, not just any output. */
  stderrIncludes: string;
};

// Each runs in an empty directory nested in an empty tmp dir, so neither
// cwd nor its parent holds a tsconfig.json, package.json, DSL or site.
const failureCases: FailureCase[] = [
  {
    label: "generate, no project",
    args: ["visualize", "generate"],
    stderrIncludes: "No TypeScript project found",
  },
  { label: "export, no DSL", args: ["visualize", "export"], stderrIncludes: "No DSL found at" },
  {
    label: "serve, no site",
    args: ["visualize", "serve"],
    stderrIncludes: "No static site found at",
  },
  {
    label: "--snapshot, no path",
    args: ["visualize", "generate", "--snapshot"],
    stderrIncludes: "--snapshot requires a file path",
  },
  {
    label: "--snapshot, missing file",
    args: ["visualize", "generate", "--snapshot", "absent.json"],
    stderrIncludes: "Snapshot error:",
  },
];

async function runFailureCase(c: FailureCase): Promise<string[]> {
  const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "e2e-viz-fail-"));
  const cwd = path.join(tmpRoot, "empty");
  fs.mkdirSync(cwd);
  try {
    const proc = Bun.spawn(["bun", POLLY_CLI, ...c.args], {
      cwd,
      stdout: "pipe",
      stderr: "pipe",
      env: { ...process.env },
    });
    const exitCode = await proc.exited;
    const stderr = await new Response(proc.stderr).text();
    const failures: string[] = [];
    if (exitCode === 0) failures.push("exited 0");
    if (!stderr.includes(c.stderrIncludes)) {
      failures.push(
        `stderr lacks "${c.stderrIncludes}"; got: ${stderr.trim().slice(-300) || "(empty)"}`
      );
    }
    return failures;
  } finally {
    fs.rmSync(tmpRoot, { recursive: true, force: true });
  }
}

/** Run every failure case, log each verdict, and return how many failed. */
async function runFailureCases(ctx: TierContext): Promise<number> {
  ctx.log("\nFailure paths (non-zero exit with a reason on stderr):");
  let failed = 0;
  for (const c of failureCases) {
    const failures = await runFailureCase(c);
    ctx.log(`  ▸ ${pad(c.label, 26)} ${failures.length === 0 ? "PASS" : "FAIL"}`);
    for (const f of failures) ctx.log(`    - ${f}`);
    if (failures.length > 0) failed++;
  }
  return failed;
}

type ColorCase = { label: string; noColor: boolean; project: boolean };

// https://no-color.org. Each run is checked both ways, so a CLI that never
// colours would fail the "colour on" case instead of passing vacuously.
const colorCases: ColorCase[] = [
  { label: "generate, colour on", noColor: false, project: true },
  { label: "generate, NO_COLOR=1", noColor: true, project: true },
  { label: "failure, NO_COLOR=1", noColor: true, project: false },
];

async function runColorCase(c: ColorCase): Promise<string[]> {
  const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "e2e-viz-color-"));
  const cwd = path.join(tmpRoot, "app");
  if (c.project) copyExample(path.join(REPO_ROOT, "examples", "minimal"), cwd);
  else fs.mkdirSync(cwd);
  try {
    const { NO_COLOR: _inherited, ...env } = process.env;
    const proc = Bun.spawn(["bun", POLLY_CLI, "visualize", "generate"], {
      cwd,
      stdout: "pipe",
      stderr: "pipe",
      env: c.noColor ? { ...env, NO_COLOR: "1" } : env,
    });
    const [exitCode, stdout, stderr] = await Promise.all([
      proc.exited,
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
    ]);
    const failures: string[] = [];
    if ((exitCode === 0) !== c.project) failures.push(`exit ${exitCode}`);
    const coloured = `${stdout}${stderr}`.includes("\x1b[");
    if (coloured === c.noColor) {
      failures.push(c.noColor ? "output has escape codes" : "output has no escape codes");
    }
    return failures;
  } finally {
    fs.rmSync(tmpRoot, { recursive: true, force: true });
  }
}

/** Run every colour case, log each verdict, and return how many failed. */
async function runColorCases(ctx: TierContext): Promise<number> {
  ctx.log("\nColour (NO_COLOR):");
  let failed = 0;
  for (const c of colorCases) {
    const failures = await runColorCase(c);
    ctx.log(`  ▸ ${pad(c.label, 26)} ${failures.length === 0 ? "PASS" : "FAIL"}`);
    for (const f of failures) ctx.log(`    - ${f}`);
    if (failures.length > 0) failed++;
  }
  return failed;
}

type CleanupCase = {
  label: string;
  /** Signal sent once the temp tsconfig exists; none = run to completion. */
  signal?: "SIGINT" | "SIGTERM";
  expectedExit: number;
  /** Plant a temp tsconfig from a dead run first; generate must replace it. */
  staleLeftover?: boolean;
};

// generate at a workspace root writes a temp tsconfig there; it must be gone
// however the run ends. The file's appearance opens the signal window: the
// analysis that follows takes most of a second.
const cleanupCases: CleanupCase[] = [
  { label: "SIGINT mid-analysis", signal: "SIGINT", expectedExit: 130 },
  { label: "SIGTERM mid-analysis", signal: "SIGTERM", expectedExit: 143 },
  { label: "stale temp tsconfig", expectedExit: 0, staleLeftover: true },
];

async function runCleanupCase(c: CleanupCase): Promise<string[]> {
  const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "e2e-viz-cleanup-"));
  const cwd = path.join(tmpRoot, "elysia-todo-app");
  copyExample(path.join(REPO_ROOT, "examples", "elysia-todo-app"), cwd);
  const tempTsConfig = path.join(cwd, WORKSPACE_TSCONFIG);
  if (c.staleLeftover) {
    // pid 2^22 + 1 is above every platform's default pid ceiling: never alive.
    const stale = { pollyVisualize: { pid: 4194305, token: "stale" }, include: [] };
    fs.writeFileSync(tempTsConfig, JSON.stringify(stale));
  }
  try {
    const proc = Bun.spawn(["bun", VISUALIZE_CLI, "generate"], {
      cwd,
      stdout: "ignore",
      stderr: "pipe",
      env: { ...process.env },
    });
    const failures: string[] = [];
    if (c.signal) {
      const deadline = Date.now() + 15_000;
      while (!fs.existsSync(tempTsConfig) && Date.now() < deadline) await Bun.sleep(5);
      if (!fs.existsSync(tempTsConfig)) failures.push("temp tsconfig never appeared");
      proc.kill(c.signal);
    }
    const exitCode = await proc.exited;
    if (exitCode !== c.expectedExit) {
      const stderr = (await new Response(proc.stderr).text()).trim().slice(-300);
      failures.push(
        `exited ${exitCode}, expected ${c.expectedExit}; stderr: ${stderr || "(empty)"}`
      );
    }
    if (fs.existsSync(tempTsConfig)) failures.push(`${WORKSPACE_TSCONFIG} left behind`);
    return failures;
  } finally {
    fs.rmSync(tmpRoot, { recursive: true, force: true });
  }
}

/** Run every temp-tsconfig cleanup case, log each verdict, and return how many failed. */
async function runCleanupCases(ctx: TierContext): Promise<number> {
  ctx.log("\nTemp tsconfig cleanup (workspace root):");
  let failed = 0;
  for (const c of cleanupCases) {
    const failures = await runCleanupCase(c);
    ctx.log(`  ▸ ${pad(c.label, 26)} ${failures.length === 0 ? "PASS" : "FAIL"}`);
    for (const f of failures) ctx.log(`    - ${f}`);
    if (failures.length > 0) failed++;
  }
  return failed;
}

// No try/catch wrapper: an unexpected throw is caught by the engine worker (and
// by selfRun when standalone), both reporting it as a failure. Keeping the body
// flat also stays under the cognitive-complexity ceiling.
export async function run(ctx: TierContext): Promise<TierResult> {
  ctx.log("E2E: polly visualize --generate\n");
  ctx.log(`  Repo:      ${REPO_ROOT}`);
  ctx.log(`  CLI entry: ${POLLY_CLI}`);
  ctx.log(`  Docker:    ${await describeDockerStatus()}`);
  ctx.log("");

  const coverageFailures = reportCoverage(ctx);
  const results = await mapPool(cases, 4, runOne);
  for (const r of results) {
    const tag = r.outcome === "passed" ? "PASS" : "FAIL";
    const validateMark =
      r.validate === "ok" ? " [validated]" : r.validate === "failed" ? " [validate ✗]" : "";
    ctx.log(`  ▸ ${pad(r.label, 28)} ${tag}${validateMark}  (${(r.elapsedMs / 1000).toFixed(1)}s)`);
  }

  ctx.log("\nDetails:");
  for (const r of results) {
    if (r.outcome === "passed") {
      fs.rmSync(r.tmpRoot, { recursive: true, force: true });
    } else {
      reportFailure(r);
    }
  }

  const failedPaths =
    (await runFailureCases(ctx)) + (await runColorCases(ctx)) + (await runCleanupCases(ctx));

  const failed =
    results.filter((r) => r.outcome !== "passed").length +
    failedPaths +
    (coverageFailures.length > 0 ? 1 : 0);
  const total = results.length + failureCases.length + colorCases.length + cleanupCases.length + 1;
  ctx.log("");
  if (failed > 0) {
    ctx.log(`${failed}/${total} failed`);
    return { pass: false, message: `${failed}/${total} visualize cases failed` };
  }
  ctx.log(`All ${total} passed`);
  return { pass: true };
}

if (import.meta.main) await selfRun(capability, run);
