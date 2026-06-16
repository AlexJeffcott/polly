/**
 * Build and serve the component gallery.
 *
 * One `Bun.build` pass of client.tsx bundles the Preact app and — through the
 * components' transitive `.module.css` imports plus the global stylesheets the
 * entry pulls in — emits a single CSS artifact (verified: ~38KB for one
 * primitive). The JS and CSS outputs are served as separate routes, or written
 * to a directory for a static export. CSS-module class hashing is deterministic
 * across builds, so the bundled JS and CSS always agree (the same property the
 * extension build relies on).
 */

import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const CLIENT_ENTRY = join(HERE, "client.tsx");
/**
 * Where build-lib.ts writes the static gallery at package-build time. Polly
 * ships only `dist`, so the published CLI can't bundle from source at runtime —
 * it serves these pre-built files instead. From the bundled CLI at
 * `dist/tools/gallery/src/`, three levels up is `dist/`, then `gallery/`.
 */
const PREBUILT_DIR = join(HERE, "..", "..", "..", "gallery");

export interface GalleryBundle {
  js: string;
  css: string;
}

/** Bundle the gallery client into a JS string and a CSS string. */
export async function buildGalleryBundle(): Promise<GalleryBundle> {
  const result = await Bun.build({
    entrypoints: [CLIENT_ENTRY],
    target: "browser",
    format: "esm",
    minify: false,
    sourcemap: "inline",
  });

  if (!result.success) {
    const logs = result.logs.map((log) => String(log)).join("\n");
    throw new Error(`gallery build failed:\n${logs}`);
  }

  let js = "";
  let css = "";
  for (const output of result.outputs) {
    const text = await output.text();
    if (output.path.endsWith(".css")) css += text;
    else js += text;
  }
  return { js, css };
}

/** The page shell — links the bundle's JS and CSS as separate files. */
function galleryHtml(): string {
  return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Polly UI gallery</title>
<link rel="stylesheet" href="./gallery.css">
</head>
<body>
<div id="app"></div>
<script type="module" src="./gallery.js"></script>
</body>
</html>
`;
}

export interface ServeOptions {
  /** Port to bind. 0 (the default) asks the OS for a free port. */
  port?: number;
}

export interface RunningGallery {
  url: string;
  port: number;
  stop: () => void;
}

/**
 * Resolve the page assets to serve. In the monorepo (source present) the client
 * is bundled fresh; in a published package (source stripped) the pre-built files
 * written by build-lib.ts are read from disk. Either way the served bytes are
 * self-contained — no source is needed at request time.
 */
async function resolveAssets(): Promise<{ html: string; js: string; css: string }> {
  if (await Bun.file(CLIENT_ENTRY).exists()) {
    const bundle = await buildGalleryBundle();
    return { html: galleryHtml(), js: bundle.js, css: bundle.css };
  }
  const indexFile = Bun.file(join(PREBUILT_DIR, "index.html"));
  if (!(await indexFile.exists())) {
    throw new Error(
      `no gallery source or pre-built bundle found (looked for ${CLIENT_ENTRY} and ${PREBUILT_DIR}). ` +
        "Rebuild the package with 'bun run build:lib'."
    );
  }
  return {
    html: await indexFile.text(),
    js: await Bun.file(join(PREBUILT_DIR, "gallery.js")).text(),
    css: await Bun.file(join(PREBUILT_DIR, "gallery.css")).text(),
  };
}

/** Build (or load) once, then serve the gallery over HTTP until `stop()`. */
export async function serveGallery(options: ServeOptions = {}): Promise<RunningGallery> {
  const { html, js, css } = await resolveAssets();
  const bundle = { js, css };

  const server = Bun.serve({
    port: options.port ?? 0,
    fetch(req) {
      const { pathname } = new URL(req.url);
      if (pathname === "/" || pathname === "/index.html") {
        return new Response(html, {
          headers: { "Content-Type": "text/html; charset=utf-8" },
        });
      }
      if (pathname === "/gallery.js") {
        return new Response(bundle.js, {
          headers: { "Content-Type": "text/javascript; charset=utf-8" },
        });
      }
      if (pathname === "/gallery.css") {
        return new Response(bundle.css, {
          headers: { "Content-Type": "text/css; charset=utf-8" },
        });
      }
      // The browser always requests a favicon; answer quietly so it doesn't
      // surface as a console error (the e2e gates on a clean console).
      if (pathname === "/favicon.ico") {
        return new Response(null, { status: 204 });
      }
      return new Response("Not found", { status: 404 });
    },
  });

  const boundPort = server.port ?? options.port ?? 0;
  return {
    url: `http://localhost:${boundPort}/`,
    port: boundPort,
    stop: () => server.stop(true),
  };
}

/** Build the gallery and write index.html + gallery.js + gallery.css to a dir. */
export async function buildGalleryToDir(outDir: string): Promise<string[]> {
  const { html, js, css } = await resolveAssets();
  const files: Array<[string, string]> = [
    ["index.html", html],
    ["gallery.js", js],
    ["gallery.css", css],
  ];
  const written: string[] = [];
  for (const [name, content] of files) {
    const path = join(outDir, name);
    await Bun.write(path, content);
    written.push(path);
  }
  return written;
}
