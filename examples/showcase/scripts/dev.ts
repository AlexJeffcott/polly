#!/usr/bin/env bun
/**
 * Showcase dev server.
 *
 * Replaces `bun --hot src/index.html` because we need a reliable
 * recursive file watcher. Bun 1.3.14 rewrote `fs.watch` on POSIX to talk
 * to the OS APIs (FSEvents on macOS, inotify on Linux) directly — but the
 * callback form can still drop or coalesce rapid event bursts during an
 * editor save. The async-iterator form from `node:fs/promises` plus a
 * debounced rebuild queue gives us the reliability we want without
 * pulling in chokidar.
 *
 * (A former `preact/compat` → `.mjs` resolve plugin is gone: preact 11
 * is ESM-only, and polly-ui no longer imports preact/compat.)
 */

import { readFileSync } from "node:fs";
import { watch } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(here, "..");
const srcDir = resolve(projectRoot, "src");
const entry = resolve(srcDir, "index.tsx");
const htmlPath = resolve(srcDir, "index.html");
const cssPath = resolve(srcDir, "showcase.css");

let bundleVersion = 0;
let cachedJs = "";
let cachedCss = "";

async function rebuild(): Promise<void> {
  const jsBuild = await Bun.build({
    entrypoints: [entry],
    target: "browser",
    format: "esm",
    minify: false,
    sourcemap: "inline",
  });
  if (!jsBuild.success) {
    process.stderr.write("[dev] JS build failed:\n");
    for (const log of jsBuild.logs) process.stderr.write(`${String(log)}\n`);
    return;
  }
  cachedJs = (await jsBuild.outputs[0]?.text()) ?? "";

  const cssBuild = await Bun.build({
    entrypoints: [cssPath],
    minify: false,
  });
  if (!cssBuild.success) {
    process.stderr.write("[dev] CSS build failed:\n");
    for (const log of cssBuild.logs) process.stderr.write(`${String(log)}\n`);
    return;
  }
  cachedCss = (await cssBuild.outputs[0]?.text()) ?? "";

  bundleVersion++;
}

await rebuild();

const clients = new Set<{ send: (m: string) => void }>();

// Debounced rebuild queue. A burst of save events (atomic save, vim's
// write+swap, multi-file format-on-save) all collapse into a single
// rebuild that fires `DEBOUNCE_MS` after the *last* event. We never run
// two rebuilds concurrently; if more events arrive mid-rebuild, the
// trailing flag triggers exactly one more pass after it completes.
const DEBOUNCE_MS = 50;
const WATCHED_EXTS = new Set([".ts", ".tsx", ".css", ".html"]);
let pendingTimer: ReturnType<typeof setTimeout> | null = null;
let rebuildInFlight: Promise<void> | null = null;
let trailing = false;

function notifyClients(): void {
  for (const client of clients) {
    try {
      client.send("reload");
    } catch {
      // client disconnected — its `close` handler will remove it.
    }
  }
}

function scheduleRebuild(): void {
  if (pendingTimer !== null) clearTimeout(pendingTimer);
  pendingTimer = setTimeout(async () => {
    pendingTimer = null;
    if (rebuildInFlight) {
      // Mark a trailing rebuild so we capture any changes that landed
      // while the previous build was running.
      trailing = true;
      return;
    }
    rebuildInFlight = (async () => {
      do {
        trailing = false;
        await rebuild();
        notifyClients();
      } while (trailing);
    })();
    try {
      await rebuildInFlight;
    } finally {
      rebuildInFlight = null;
    }
  }, DEBOUNCE_MS);
}

// Watch in the background; the main script proceeds to start the
// server. Each event from the async iterator triggers a debounced
// rebuild — see comment above for ordering guarantees.
(async () => {
  const watcher = watch(srcDir, { recursive: true });
  for await (const event of watcher) {
    if (!event.filename) continue;
    const dot = event.filename.lastIndexOf(".");
    if (dot === -1) continue;
    const ext = event.filename.slice(dot);
    if (!WATCHED_EXTS.has(ext)) continue;
    scheduleRebuild();
  }
})().catch((err: unknown) => {
  process.stderr.write(`[dev] watcher crashed: ${String(err)}\n`);
});

const HMR_CLIENT = `
const ws = new WebSocket("ws://" + location.host + "/_dev/ws");
ws.onmessage = (e) => { if (e.data === "reload") location.reload(); };
`;

function renderHtml(): string {
  const raw = readFileSync(htmlPath, "utf8");
  return raw
    .replace('href="./showcase.css"', `href="/showcase.css?v=${bundleVersion}"`)
    .replace('src="./index.tsx"', `src="/index.js?v=${bundleVersion}"`)
    .replace("</body>", `<script>${HMR_CLIENT}</script></body>`);
}

const PORT = Number(process.env.PORT ?? 3000);
const server = Bun.serve({
  port: PORT,
  fetch(req, srv) {
    const url = new URL(req.url);
    if (url.pathname === "/_dev/ws") {
      if (srv.upgrade(req)) return undefined;
      return new Response("upgrade required", { status: 426 });
    }
    if (url.pathname === "/" || url.pathname === "/index.html") {
      return new Response(renderHtml(), { headers: { "Content-Type": "text/html" } });
    }
    if (url.pathname === "/index.js") {
      return new Response(cachedJs, { headers: { "Content-Type": "text/javascript" } });
    }
    if (url.pathname === "/showcase.css") {
      return new Response(cachedCss, { headers: { "Content-Type": "text/css" } });
    }
    return new Response("not found", { status: 404 });
  },
  websocket: {
    open(ws) {
      clients.add(ws);
    },
    close(ws) {
      clients.delete(ws);
    },
    message() {
      // no client → server messages today
    },
  },
});

console.log(`[dev] showcase ready at http://localhost:${server.port}/`);
