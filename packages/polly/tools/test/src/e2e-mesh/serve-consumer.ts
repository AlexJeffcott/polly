/**
 * @fairfox/polly/test/e2e-mesh — bundle and serve the e2e consumer.
 *
 * Bun.build compiles `examples/e2e-consumer/main.ts` for the browser
 * target with the Automerge base64 fix (same plugin the existing browser
 * runner uses). Bun.serve then hands the HTML on "/" with a bootstrap
 * shim injected, and the JS on "/main.js". Puppeteer points at the
 * returned URL.
 *
 * The kit owns this so every e2e script gets the same boot path: build
 * the in-tree consumer, serve from a fresh ephemeral port, inject the
 * peer-specific bootstrap. No script should call Bun.build directly —
 * keeping it in one place means the Automerge plugin and the bootstrap
 * shape stay coherent across the suite.
 */

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import type { BunPlugin } from "bun";

const repoRoot = resolve(__dirname, "../../../..");
const consumerEntry = resolve(repoRoot, "examples/e2e-consumer/main.ts");
const consumerHtml = resolve(repoRoot, "examples/e2e-consumer/index.html");
const automergeBase64Path = resolve(
  repoRoot,
  "node_modules/@automerge/automerge/dist/mjs/entrypoints/fullfat_base64.js"
);

const automergeBase64Plugin: BunPlugin = {
  name: "automerge-base64",
  setup(build) {
    build.onResolve({ filter: /^@automerge\/automerge(\/slim)?$/ }, () => ({
      path: automergeBase64Path,
    }));
  },
};

export interface ServeConsumerOptions {
  /** The bootstrap object that the page reads from window.__pollyE2eBootstrap. */
  bootstrap: Record<string, unknown>;
}

export interface ServeConsumerResult {
  /** http://127.0.0.1:<port>/ — pass to puppeteer page.goto. */
  url: string;
  /** Stop the server. Idempotent. */
  close: () => Promise<void>;
}

/**
 * Bundle the consumer and serve it on an ephemeral port. The HTML's
 * `<script type="module" src="./main.js">` resolves to the freshly built
 * bundle; the bootstrap shim is inserted right before it so the global
 * is set by the time `main.ts` reads it.
 */
export async function serveConsumer(options: ServeConsumerOptions): Promise<ServeConsumerResult> {
  const buildResult = await Bun.build({
    entrypoints: [consumerEntry],
    target: "browser",
    format: "esm",
    minify: false,
    sourcemap: "inline",
    plugins: [automergeBase64Plugin],
  });
  if (!buildResult.success) {
    const logs = buildResult.logs.map((log) => String(log)).join("\n");
    throw new Error(`serveConsumer: build failed:\n${logs}`);
  }
  const jsText = await buildResult.outputs[0]?.text();
  if (!jsText) {
    throw new Error("serveConsumer: build produced no output");
  }

  const rawHtml = readFileSync(consumerHtml, "utf-8");
  const bootstrapJson = JSON.stringify(options.bootstrap);
  const bootstrapShim = `<script>window.__pollyE2eBootstrap = ${bootstrapJson};</script>`;
  const html = rawHtml.replace(
    /<script type="module" src="\.\/main\.js"><\/script>/,
    `${bootstrapShim}\n    <script type="module" src="./main.js"></script>`
  );

  const server = Bun.serve({
    port: 0,
    fetch(req) {
      const url = new URL(req.url);
      if (url.pathname === "/" || url.pathname === "/index.html") {
        return new Response(html, { headers: { "Content-Type": "text/html" } });
      }
      if (url.pathname === "/main.js") {
        return new Response(jsText, {
          headers: { "Content-Type": "application/javascript" },
        });
      }
      return new Response("not found", { status: 404 });
    },
  });

  return {
    url: `http://127.0.0.1:${server.port}/`,
    close: async () => {
      server.stop();
    },
  };
}
