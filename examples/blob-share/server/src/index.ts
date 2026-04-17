/**
 * Blob-share example server.
 *
 * Serves the client HTML + bundled JS, and runs Polly's stateless
 * signalling server so two browser tabs can discover each other over
 * WebRTC. The server sees SDP/ICE exchange during connection setup and
 * nothing else — no blob bytes, no files, no document state.
 */

import { join } from "node:path";
import { html } from "@elysiajs/html";
import { signalingServer } from "@fairfox/polly/elysia";
import { Elysia } from "elysia";

const CLIENT_ENTRY = join(import.meta.dir, "../../client/src/main.ts");
const CLIENT_HTML = join(import.meta.dir, "../../client/src/index.html");

// Cast around elysia type mismatch between the example's installed
// version and polly's peer-dep version. Both resolve to the same runtime.
const app = new Elysia()
  .use(html())
  .use(signalingServer({ path: "/polly/signaling" }) as any)
  .get("/", async () => {
    return Bun.file(CLIENT_HTML).text();
  })
  .get("/main.js", async () => {
    const result = await Bun.build({
      entrypoints: [CLIENT_ENTRY],
      target: "browser",
      format: "esm",
      minify: process.env.NODE_ENV === "production",
    });
    if (!result.success) {
      console.error("Build failed:", result.logs);
      return new Response("Build failed", { status: 500 });
    }
    const output = result.outputs[0];
    if (!output) return new Response("No output", { status: 500 });
    return new Response(await output.text(), {
      headers: { "Content-Type": "application/javascript" },
    });
  })
  .listen(3100);

console.log(`🎯 blob-share running at http://localhost:${app.server?.port}`);
console.log(`   Open two browser tabs and drop files to share peer-to-peer.`);
