#!/usr/bin/env bun
// Entry for `polly visualize`. It checks the optional tool packages before main.ts
// loads them: main.ts imports them statically, so a missing one would stop
// it with a bare "Cannot find module" before any of its code ran. The
// specifier is computed so that `bun build` keeps main.js a separate file.

import { exitIfMissingToolPackages } from "../../tool-deps/src/index.ts";

exitIfMissingToolPackages("visualize", process.argv.slice(2), import.meta.dir);
await import(
  new URL(import.meta.url.endsWith(".js") ? "./main.js" : "./main.ts", import.meta.url).href
);
