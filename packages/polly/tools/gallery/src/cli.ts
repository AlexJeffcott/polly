#!/usr/bin/env bun
/**
 * `polly gallery` — serve (or statically export) the polly-ui component gallery.
 *
 *   polly gallery                 # serve at http://localhost:4321
 *   polly gallery --port 5000     # serve on a chosen port
 *   polly gallery --open          # serve and open the default browser
 *   polly gallery --build <dir>   # write a static index.html + js + css
 *
 * Hand-rolled arg parsing, matching the other polly tool CLIs.
 */

import { buildGalleryToDir, serveGallery } from "./server.ts";

const DEFAULT_PORT = 4321;

function printHelp(): void {
  console.log(`polly gallery — preview every polly-ui primitive in one page.

Usage:
  polly gallery [--port <n>] [--open]   Serve the gallery (default port ${DEFAULT_PORT})
  polly gallery --build <dir>           Write a static gallery to <dir>
  polly gallery --help                  Show this help

One page that renders every polly-ui primitive: the single place to see the
components, the render surface the visual-regression baselines capture, and a
gap-check that fails when a registered primitive has no specimen.`);
}

/** Read the value following a flag, erroring if it is missing or another flag. */
function flagValue(args: string[], flag: string): string | undefined {
  const idx = args.indexOf(flag);
  if (idx === -1) return undefined;
  const value = args[idx + 1];
  if (value === undefined || value.startsWith("-")) {
    console.log(`error: ${flag} requires a value`);
    process.exit(1);
  }
  return value;
}

function openBrowser(url: string): void {
  const command =
    process.platform === "darwin"
      ? ["open", url]
      : process.platform === "win32"
        ? ["cmd", "/c", "start", "", url]
        : ["xdg-open", url];
  try {
    Bun.spawn(command, { stdout: "ignore", stderr: "ignore" });
  } catch {
    // Opening the browser is best-effort; the URL is printed regardless.
  }
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);

  if (args.includes("--help") || args.includes("-h")) {
    printHelp();
    return;
  }

  const buildDir = flagValue(args, "--build");
  if (buildDir !== undefined) {
    const files = await buildGalleryToDir(buildDir);
    console.log(`Gallery written to ${buildDir}:`);
    for (const file of files) console.log(`  ${file}`);
    return;
  }

  const portArg = flagValue(args, "--port");
  const port = portArg === undefined ? DEFAULT_PORT : Number(portArg);
  if (!Number.isInteger(port) || port < 0 || port > 65535) {
    console.log(`error: --port must be an integer in 0–65535 (got "${portArg}")`);
    process.exit(1);
  }

  let gallery: Awaited<ReturnType<typeof serveGallery>>;
  try {
    gallery = await serveGallery({ port });
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.log(`error: could not start the gallery server: ${message}`);
    if (/EADDRINUSE|in use|address already/i.test(message)) {
      console.log(`Port ${port} is in use — try 'polly gallery --port <other>'.`);
    }
    process.exit(1);
  }

  console.log(`Polly UI gallery → ${gallery.url}`);
  console.log("Serving the polly-ui component gallery. Press Ctrl-C to stop.");
  if (args.includes("--open")) openBrowser(gallery.url);

  const shutdown = (): void => {
    gallery.stop();
    process.exit(0);
  };
  process.on("SIGINT", shutdown);
  process.on("SIGTERM", shutdown);
}

main().catch((error) => {
  console.log(error);
  process.exit(1);
});
