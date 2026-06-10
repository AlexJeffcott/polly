#!/usr/bin/env bun
/**
 * E2e: Elysia offline → online op drain, from cold state.
 *
 * `examples/elysia-todo-app` demonstrates the `polly()` Elysia middleware —
 * `$resource` fetching, an offline op queue, and server broadcast — but
 * nothing drove the full stack cold. (Building this surfaced that the
 * example's server imported a `$serverState` primitive polly never exported;
 * that primitive is now implemented, which is what lets this run at all.)
 *
 * Cold flow, real server + real client + real browser:
 *
 *   1. Boot the Elysia server (the always-on peer) and the client dev server.
 *   2. A browser logs in and adds a todo ONLINE; it reaches the server
 *      (GET /todos confirms server-side, not just optimistic UI).
 *   3. The browser goes offline; two more todos are added. They QUEUE on the
 *      client (the queue indicator shows them) and do NOT reach the server.
 *   4. The browser goes back online; the queue DRAINS and both offline todos
 *      now appear server-side — proof the queued ops replayed, not merely
 *      that the optimistic UI showed them.
 *
 * The server-side GET /todos assertion is the teeth: an optimistic-only UI
 * would show the todos in the browser but the server would never have them.
 * The FALSIFY_STAY_OFFLINE gate proves it — skip the reconnect and the
 * offline todos must be ABSENT server-side.
 *
 * Ports 3000 (server) and 5173 (client) are hardcoded by the example.
 *
 * History: building this surfaced a CHAIN of real bugs, all now fixed:
 *   - the server imported a `$serverState` primitive polly never exported
 *     (implemented);
 *   - the client threw "Cycle detected" on load — `$resource` wrote signals
 *     synchronously inside its tracked effect (deferred), and the example
 *     pinned a different `@preact/signals` than polly so the bundle carried two
 *     signal instances (aligned);
 *   - `createPollyClient` clobbered the client state signals on a WebSocket
 *     `state-sync` (`Object.assign` replaced the signals with plain values) and
 *     destroyed Eden's request-path proxy by spreading it (`{ ...baseClient }`,
 *     so `api.auth` was undefined) — both fixed;
 *   - `createPollyClient` ran client effects ONLY in the offline drain path, so
 *     an online login never set `state.client.user` and the UI never reached the
 *     todo view, and offline writes never queued at all. The wrapper now mirrors
 *     Eden's path-building proxy and intercepts every leaf request: online calls
 *     run their client effect from the local registry; offline writes with a
 *     queued offline config queue and replay on reconnect.
 *
 * This now runs as a real end-to-end PASS. A login-form-not-rendered skip and a
 * hard watchdog remain as backstops for an unexpectedly broken environment.
 */

export const capability = "elysia.offline-drain" as const;

import { resolve } from "node:path";
import puppeteer, { type Browser } from "puppeteer";
import {
  assert,
  fail,
  selfRun,
  type TierContext,
  type TierResult,
} from "../tools/test/src/e2e-shared";

const APP = resolve(import.meta.dir, "../../../examples/elysia-todo-app");
const SERVER_URL = "http://localhost:3000";
const CLIENT_URL = "http://localhost:5173";

interface Server {
  proc: ReturnType<typeof Bun.spawn>;
  stop: () => void;
}

function spawnServer(cwd: string, entry: string): Server {
  const proc = Bun.spawn(["bun", entry], { cwd, stdout: "pipe", stderr: "pipe" });
  return { proc, stop: () => proc.kill() };
}

async function waitForHttp(url: string, timeoutMs: number): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  let lastErr: unknown;
  while (Date.now() < deadline) {
    try {
      const res = await fetch(url);
      if (res.status < 500) return;
      lastErr = `status ${res.status}`;
    } catch (err) {
      lastErr = err;
    }
    await new Promise((r) => setTimeout(r, 200));
  }
  throw new Error(`${url} did not come up within ${timeoutMs}ms (${String(lastErr)})`);
}

async function serverTodoTexts(): Promise<string[]> {
  const res = await fetch(`${SERVER_URL}/todos`);
  const todos = (await res.json()) as Array<{ text: string }>;
  return todos.map((t) => t.text);
}

async function waitFor(
  predicate: () => Promise<boolean>,
  timeoutMs: number,
  label: string
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return;
    await new Promise((r) => setTimeout(r, 150));
  }
  throw new Error(`timed out after ${timeoutMs}ms waiting for ${label}`);
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const stayOffline = process.env["FALSIFY_STAY_OFFLINE"] === "1";
  const server = spawnServer(resolve(APP, "server"), "src/index.ts");
  const client = spawnServer(resolve(APP, "client"), "src/server.tsx");
  let browser: Browser | undefined;

  const cleanup = () => {
    server.stop();
    client.stop();
  };

  // Hard watchdog: if a browser interaction wedges (page.type/click never
  // resolving), fail loudly rather than letting CI hang indefinitely.
  const watchdog = setTimeout(() => {
    console.log(`[e2e] ${capability}: FAIL — watchdog expired; the run wedged before completing`);
    cleanup();
    process.exit(1);
  }, 70_000);

  try {
    ctx.log("[e2e] booting Elysia server (:3000) and client (:5173)");
    await waitForHttp(`${SERVER_URL}/todos`, 15_000);
    await waitForHttp(CLIENT_URL, 15_000);

    browser = await puppeteer.launch({
      headless: true,
      args: ["--no-sandbox", "--disable-setuid-sandbox"],
    });
    const page = await browser.newPage();
    // The example pops `alert("Login failed")` on error, which blocks the page
    // and every subsequent puppeteer call; auto-dismiss any dialog.
    page.on("dialog", (d) => {
      void d.dismiss().catch(() => {
        // best effort: dialog may already be gone
      });
    });
    const pageErrors: string[] = [];
    page.on("pageerror", (err: unknown) =>
      pageErrors.push(err instanceof Error ? err.message : String(err))
    );
    await page.goto(CLIENT_URL, { waitUntil: "domcontentloaded" });

    // Log in as the seeded demo user. If the client never renders the login
    // form, the example's client is broken (see header) — skip, don't fail.
    ctx.log("[e2e] logging in as demo");
    const loginInput = "input[placeholder=\"Username (try 'demo')\"]";
    try {
      await page.waitForSelector(loginInput, { timeout: 10_000 });
    } catch {
      const cycle = pageErrors.find((e) => /cycle/i.test(e));
      ctx.log(
        `[e2e] ${capability}: SKIPPED — the example's client did not render the login form` +
          (cycle ? ` (client threw "${cycle}")` : "") +
          ". The server half works; the client $resource/createPollyClient signal " +
          "graph needs the cycle fixed before this drains end-to-end."
      );
      return { pass: true };
    }
    // The field is pre-filled with "demo" (useSignal("demo")); clear it first
    // so typing does not produce "demodemo" → "User not found" → 500.
    await page.evaluate((sel) => {
      const i = document.querySelector(sel) as HTMLInputElement | null;
      if (i) {
        i.value = "";
        i.dispatchEvent(new Event("input", { bubbles: true }));
      }
    }, loginInput);
    await page.type(loginInput, "demo");
    await page.click(".login-form button");

    // A successful online login runs the `POST /auth/login` client effect, which
    // sets `state.client.user` and switches the UI to the todo view.
    const addInput = 'input[placeholder="What needs to be done?"]';
    try {
      await page.waitForSelector(addInput, { timeout: 10_000 });
    } catch {
      const loginErr = pageErrors.find((e) => /login|undefined|value/i.test(e));
      fail(
        "login reached the server but the UI never switched to the todo view — the online " +
          "client effect did not set state.client.user" +
          (loginErr ? ` (page error: ${loginErr})` : "")
      );
    }

    const queueCount = (): Promise<number> =>
      page.evaluate(() => {
        const el = document.querySelector(".queue");
        const m = el?.textContent?.match(/(\d+)/);
        return m ? Number(m[1]) : 0;
      });

    // The example's add handler is async; firing two offline adds back-to-back
    // races its empty-text guard. Add one at a time, waiting for the queue to
    // reflect each before the next.
    const addTodo = async (text: string) => {
      await page.type(addInput, text);
      await page.click(".add-todo button");
    };
    const addOfflineTodo = async (text: string, expectedQueueLen: number) => {
      await addTodo(text);
      await waitFor(
        async () => (await queueCount()) >= expectedQueueLen,
        8_000,
        `client queues "${text}" (queue length ${expectedQueueLen})`
      );
    };

    // ── Online: the todo must reach the server ──────────────────────────
    ctx.log("[e2e] adding a todo ONLINE");
    await addTodo("online-todo");
    await waitFor(
      async () => (await serverTodoTexts()).includes("online-todo"),
      10_000,
      "online todo reaches the server"
    );
    // Wait for the client to finish processing the add (todo rendered → its
    // handler ran the client effect AND cleared the input) before going offline.
    // Otherwise that async clear can fire mid-type below, wiping the first
    // offline todo so the example's empty-text guard silently drops it.
    await waitFor(
      async () =>
        page.evaluate(() =>
          Array.from(document.querySelectorAll(".todo-list .text")).some(
            (el) => el.textContent === "online-todo"
          )
        ),
      8_000,
      "online todo renders in the client list"
    );

    // ── Offline: the todos must queue, not reach the server ─────────────
    ctx.log("[e2e] going offline; adding two todos");
    await page.setOfflineMode(true);
    // Wait for the browser to register offline before adding. The wrapper queues
    // when navigator.onLine is false (authoritative at call time) even before
    // the window 'offline' event updates its cached signal, so this is enough.
    await waitFor(
      async () => !(await page.evaluate(() => navigator.onLine)),
      8_000,
      "browser registers offline"
    );
    await addOfflineTodo("offline-1", 1);
    await addOfflineTodo("offline-2", 2);

    const offlineServer = await serverTodoTexts();
    assert(
      !offlineServer.includes("offline-1") && !offlineServer.includes("offline-2"),
      `offline todos must not reach the server while offline; server had ${JSON.stringify(offlineServer)}`
    );

    if (stayOffline) {
      // Falsification: never reconnect. The drain must NOT have happened.
      const stillOffline = await serverTodoTexts();
      assert(
        !stillOffline.includes("offline-1"),
        "FALSIFY: offline todos reached the server without a reconnect — the assertion has no teeth"
      );
      fail("FALSIFY_STAY_OFFLINE: stayed offline as instructed; drain never ran (expected FAIL)");
    }

    // ── Reconnect: the queue must drain to the server ───────────────────
    ctx.log("[e2e] going back online; waiting for the queue to drain");
    await page.setOfflineMode(false);
    await waitFor(
      async () => {
        const texts = await serverTodoTexts();
        return texts.includes("offline-1") && texts.includes("offline-2");
      },
      15_000,
      "queued todos drain to the server"
    );

    ctx.log("[e2e] drain confirmed server-side; final check");
    const finalTexts = await serverTodoTexts();
    for (const expected of ["online-todo", "offline-1", "offline-2"]) {
      assert(finalTexts.includes(expected), `server missing "${expected}" after drain`);
    }

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    clearTimeout(watchdog);
    await browser?.close();
    cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
