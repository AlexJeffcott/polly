/**
 * @fairfox/polly/test/e2e-mesh — launchPeer.
 *
 * Boots one Puppeteer-controlled Chrome instance with a fresh profile
 * directory (deleted before launch), navigates to the served consumer,
 * wires console + pageerror handlers, and waits for the consumer to
 * report `ready` status. Returns a handle the e2e script drives.
 *
 * The fresh-profile guarantee is what makes "cold start" honest —
 * every run begins with empty IndexedDB, empty localStorage, empty
 * service-worker registrations. A real first-install user sees the
 * same state.
 */

import { existsSync, mkdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { resolve } from "node:path";
import puppeteer, { type Browser, type Page } from "puppeteer";
import type {
  MeshDiagnostic,
  MeshDiagnosticEvent,
} from "../../../../src/shared/lib/mesh-diagnostics";
import {
  type ConsolePattern,
  isAllowedConsoleLine,
  MESH_CONSOLE_ALLOWLIST,
} from "./console-allowlist";
import { MeshAssertionError } from "./mesh-assertions";

export interface CapturedConsoleLine {
  level: string;
  text: string;
  /** True when the line matched the supplied allowlist; allowed lines do
   *  not contribute to assertNoUnexpectedConsole failures. */
  allowed: boolean;
}

export interface LaunchedPeer {
  /** The peerId the consumer was booted with. */
  readonly peerId: string;
  /** The Puppeteer Page handle. Scripts drive this directly. */
  readonly page: Page;
  /** The Puppeteer Browser handle. Scripts that need a second tab in
   *  the same profile call `browser.newPage()` (or use the kit's
   *  {@link launchSecondTab} helper, which adds the same console + ready
   *  wiring launchPeer applies to the first tab). */
  readonly browser: Browser;
  /** Live capture buffer of console lines seen on this peer. */
  readonly console: ReadonlyArray<CapturedConsoleLine>;
  /** Live capture of page-level errors. */
  readonly pageErrors: ReadonlyArray<string>;
  /** Throws if any captured console line was not allowed. */
  assertNoUnexpectedConsole: () => void;
  /**
   * Read every mesh-diagnostic event the consumer has captured so far.
   * Each call snapshots the live browser-side buffer; the array is
   * detached from the page after read.
   */
  collectDiagnostics: () => Promise<MeshDiagnosticEvent[]>;
  /**
   * Read the captured diagnostics and assert no unexpected silent
   * drops fired. Pass `allow` with the drop-kinds the scenario
   * legitimately expects; anything else fails.
   */
  assertNoSilentDrops: (allow?: ReadonlyArray<MeshDiagnostic["kind"]>) => Promise<void>;
  /** Close the page, browser, and profile dir. Idempotent. */
  close: () => Promise<void>;
}

export interface LaunchPeerOptions {
  /** Peer id used in the consumer's display + key wiring. */
  peerId: string;
  /** http://127.0.0.1:<port>/ from serveConsumer. */
  consumerUrl: string;
  /** When true, run Chrome headfully so the developer can watch. Defaults
   *  to `process.env.HEADLESS !== "false"`. */
  headless?: boolean;
  /** Override the console allowlist; defaults to MESH_CONSOLE_ALLOWLIST. */
  consoleAllowlist?: ReadonlyArray<ConsolePattern>;
  /** Cap how long to wait for the consumer to report the ready status
   *  before throwing. Defaults to 15s. */
  readyTimeoutMs?: number;
  /** Override the profile-dir parent. Defaults to os.tmpdir() / polly-e2e. */
  profileParent?: string;
  /** The status sentinel the consumer reports when it is ready for the
   *  script to drive it. Defaults to "ready" (the prebaked path, where
   *  the mesh client is up). The pairing path passes "awaiting-pairing":
   *  the consumer is booted with its hooks installed but has deferred the
   *  mesh join until the script drives the token exchange. */
  readyStatus?: string;
}

const READY_POLL_MS = 100;

function profileDir(parent: string, peerId: string): string {
  const safePeerId = peerId.replace(/[^a-zA-Z0-9_-]/g, "_");
  return resolve(parent, `polly-e2e-${safePeerId}-${Date.now()}`);
}

/**
 * Launch one peer and wait until the consumer reports it is connected
 * and rendering. Throws on console-error or pageerror during boot.
 */
export async function launchPeer(options: LaunchPeerOptions): Promise<LaunchedPeer> {
  const {
    peerId,
    consumerUrl,
    headless = process.env["HEADLESS"] !== "false",
    consoleAllowlist = MESH_CONSOLE_ALLOWLIST,
    readyTimeoutMs = 15_000,
    profileParent = resolve(tmpdir(), "polly-e2e"),
    readyStatus = "ready",
  } = options;

  if (!existsSync(profileParent)) mkdirSync(profileParent, { recursive: true });
  const userDataDir = profileDir(profileParent, peerId);
  if (existsSync(userDataDir)) {
    rmSync(userDataDir, { recursive: true, force: true });
  }

  const browser: Browser = await puppeteer.launch({
    headless,
    userDataDir,
    args: ["--no-sandbox", "--disable-setuid-sandbox"],
  });
  const page = await browser.newPage();

  const consoleLines: CapturedConsoleLine[] = [];
  const pageErrors: string[] = [];

  page.on("console", (msg) => {
    const level = msg.type();
    const text = msg.text();
    const allowed = isAllowedConsoleLine({ level, text }, consoleAllowlist);
    consoleLines.push({ level, text, allowed });
  });
  page.on("pageerror", (err) => {
    pageErrors.push(err instanceof Error ? err.message : String(err));
  });

  await page.goto(consumerUrl, { waitUntil: "domcontentloaded" });

  const deadline = Date.now() + readyTimeoutMs;
  let ready = false;
  let lastStatus = "";
  while (Date.now() < deadline) {
    lastStatus = await page.evaluate(
      () => document.querySelector("[data-e2e='status']")?.textContent ?? ""
    );
    if (lastStatus === readyStatus) {
      ready = true;
      break;
    }
    if (lastStatus.startsWith("error") || lastStatus.startsWith("bootstrap-failed")) {
      await browser.close();
      rmSync(userDataDir, { recursive: true, force: true });
      throw new Error(`launchPeer(${peerId}): consumer reported "${lastStatus}"`);
    }
    await new Promise((r) => setTimeout(r, READY_POLL_MS));
  }

  if (!ready) {
    await browser.close();
    rmSync(userDataDir, { recursive: true, force: true });
    throw new Error(
      `launchPeer(${peerId}): consumer did not reach "${readyStatus}" within ${readyTimeoutMs}ms (last status: "${lastStatus}")`
    );
  }

  function assertNoUnexpectedConsole(): void {
    const bad = consoleLines.filter(
      (line) =>
        !line.allowed &&
        (line.level === "error" || line.level === "warn" || line.level === "warning")
    );
    if (bad.length > 0) {
      const summary = bad.map((l) => `  [${l.level}] ${l.text}`).join("\n");
      throw new Error(`launchPeer(${peerId}): unexpected console output:\n${summary}`);
    }
    if (pageErrors.length > 0) {
      throw new Error(
        `launchPeer(${peerId}): page errors:\n${pageErrors.map((e) => `  ${e}`).join("\n")}`
      );
    }
  }

  async function collectDiagnostics(): Promise<MeshDiagnosticEvent[]> {
    const events = await page.evaluate(() => {
      const w = window as unknown as { __pollyE2eDiagnostics?: MeshDiagnosticEvent[] };
      return w.__pollyE2eDiagnostics ? [...w.__pollyE2eDiagnostics] : [];
    });
    return events;
  }

  async function assertNoSilentDrops(
    allow: ReadonlyArray<MeshDiagnostic["kind"]> = []
  ): Promise<void> {
    const allowed = new Set(allow);
    const events = await collectDiagnostics();
    const unexpected = events.filter(
      (event) => event.kind.startsWith("drop:") && !allowed.has(event.kind)
    );
    if (unexpected.length === 0) return;
    const summary = unexpected
      .map((event) => {
        const { kind, timestamp: _ts, ...rest } = event;
        return `  ${kind} ${JSON.stringify(rest)}`;
      })
      .join("\n");
    throw new MeshAssertionError(
      `launchPeer(${peerId}): unexpected silent-drop diagnostics fired during the e2e run.\n${summary}\n` +
        `If a drop kind is legitimately expected, pass it to peer.assertNoSilentDrops([...]).`,
      unexpected
    );
  }

  let closed = false;
  return {
    peerId,
    page,
    browser,
    console: consoleLines,
    pageErrors,
    assertNoUnexpectedConsole,
    collectDiagnostics,
    assertNoSilentDrops,
    close: async () => {
      if (closed) return;
      closed = true;
      try {
        await page.close();
      } catch {
        // page may already be detached if browser closed
      }
      try {
        await browser.close();
      } catch {
        // best effort
      }
      try {
        rmSync(userDataDir, { recursive: true, force: true });
      } catch {
        // best effort
      }
    },
  };
}

export interface LaunchSecondTabOptions {
  /** http://127.0.0.1:<port>/ from serveConsumer. Pass the same URL the
   *  primary tab loaded so the new tab boots with the same bootstrap
   *  shim and shares IndexedDB on the existing profile. */
  consumerUrl: string;
  /** Override the console allowlist; defaults to MESH_CONSOLE_ALLOWLIST. */
  consoleAllowlist?: ReadonlyArray<ConsolePattern>;
  /** Cap how long to wait for the second tab to reach status="ready". */
  readyTimeoutMs?: number;
}

/**
 * Open a second tab inside an existing peer's Puppeteer browser. Boots
 * the same consumer (same URL, same bootstrap shim, same identity)
 * and returns a {@link LaunchedPeer} handle whose `close` only
 * detaches the page — the parent peer owns the browser lifecycle, so
 * shutting the tab does not tear the original peer down.
 *
 * Used by the multi-tab coherence script (RFC-043 adjacent surface,
 * Phase 2). Tabs share IndexedDB, which is what makes the test
 * interesting: two `MeshClient` instances on disjoint memory speaking
 * to the same persisted Automerge state.
 */
export async function launchSecondTab(
  parent: LaunchedPeer,
  options: LaunchSecondTabOptions
): Promise<LaunchedPeer> {
  const {
    consumerUrl,
    consoleAllowlist = MESH_CONSOLE_ALLOWLIST,
    readyTimeoutMs = 15_000,
  } = options;
  const page = await parent.browser.newPage();

  const consoleLines: CapturedConsoleLine[] = [];
  const pageErrors: string[] = [];
  page.on("console", (msg) => {
    const level = msg.type();
    const text = msg.text();
    const allowed = isAllowedConsoleLine({ level, text }, consoleAllowlist);
    consoleLines.push({ level, text, allowed });
  });
  page.on("pageerror", (err) => {
    pageErrors.push(err instanceof Error ? err.message : String(err));
  });

  await page.goto(consumerUrl, { waitUntil: "domcontentloaded" });
  const deadline = Date.now() + readyTimeoutMs;
  let ready = false;
  let lastStatus = "";
  while (Date.now() < deadline) {
    lastStatus = await page.evaluate(
      () => document.querySelector("[data-e2e='status']")?.textContent ?? ""
    );
    if (lastStatus === "ready") {
      ready = true;
      break;
    }
    if (lastStatus.startsWith("error") || lastStatus.startsWith("bootstrap-failed")) {
      await page.close();
      throw new Error(`launchSecondTab(${parent.peerId}): consumer reported "${lastStatus}"`);
    }
    await new Promise((r) => setTimeout(r, READY_POLL_MS));
  }
  if (!ready) {
    await page.close();
    throw new Error(
      `launchSecondTab(${parent.peerId}): consumer did not reach "ready" within ${readyTimeoutMs}ms (last status: "${lastStatus}")`
    );
  }

  function assertNoUnexpectedConsole(): void {
    const bad = consoleLines.filter(
      (line) =>
        !line.allowed &&
        (line.level === "error" || line.level === "warn" || line.level === "warning")
    );
    if (bad.length > 0) {
      const summary = bad.map((l) => `  [${l.level}] ${l.text}`).join("\n");
      throw new Error(`launchSecondTab(${parent.peerId}): unexpected console output:\n${summary}`);
    }
    if (pageErrors.length > 0) {
      throw new Error(
        `launchSecondTab(${parent.peerId}): page errors:\n${pageErrors.map((e) => `  ${e}`).join("\n")}`
      );
    }
  }

  async function collectDiagnostics(): Promise<MeshDiagnosticEvent[]> {
    return page.evaluate(() => {
      const w = window as unknown as { __pollyE2eDiagnostics?: MeshDiagnosticEvent[] };
      return w.__pollyE2eDiagnostics ? [...w.__pollyE2eDiagnostics] : [];
    });
  }

  async function assertNoSilentDrops(
    allow: ReadonlyArray<MeshDiagnostic["kind"]> = []
  ): Promise<void> {
    const allowed = new Set(allow);
    const events = await collectDiagnostics();
    const unexpected = events.filter(
      (event) => event.kind.startsWith("drop:") && !allowed.has(event.kind)
    );
    if (unexpected.length === 0) return;
    const summary = unexpected
      .map((event) => {
        const { kind, timestamp: _ts, ...rest } = event;
        return `  ${kind} ${JSON.stringify(rest)}`;
      })
      .join("\n");
    throw new MeshAssertionError(
      `launchSecondTab(${parent.peerId}): unexpected silent-drop diagnostics fired during the e2e run.\n${summary}`,
      unexpected
    );
  }

  let closed = false;
  return {
    peerId: parent.peerId,
    page,
    browser: parent.browser,
    console: consoleLines,
    pageErrors,
    assertNoUnexpectedConsole,
    collectDiagnostics,
    assertNoSilentDrops,
    close: async () => {
      if (closed) return;
      closed = true;
      try {
        await page.close();
      } catch {
        // best effort
      }
    },
  };
}
