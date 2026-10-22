/**
 * The mutant for a bundle. The test preload (preload.ts) reaches Bun
 * processes only; a command that bundles a page (`Bun.build`) and tests it in
 * a browser loads the target through the bundler, so without this plugin
 * every mutant survives.
 *
 *   await Bun.build({ entrypoints, plugins: [pollyMutatePlugin()] });
 *
 * With POLLY_MUTATE_FILE and POLLY_MUTATE_SPAN set (the engine sets both for
 * each mutant run) the plugin serves the target's mutated text; with either
 * unset it does nothing, so a build can keep it on.
 */
import { readFileSync } from "node:fs";
import type { BunPlugin } from "bun";
import { exactly, loaderFor, mutatedText, parseSpan } from "./mutant-text.ts";

export function pollyMutatePlugin(
  env: Record<string, string | undefined> = process.env
): BunPlugin {
  const target = env["POLLY_MUTATE_FILE"];
  const rawSpan = env["POLLY_MUTATE_SPAN"];
  return {
    name: "polly-mutate-bundle",
    setup(build) {
      if (!target || !rawSpan) return;
      const contents = mutatedText(readFileSync(target, "utf8"), parseSpan(rawSpan));
      const loader = loaderFor(target);
      build.onLoad({ filter: exactly([target]) }, () => ({ contents, loader }));
    },
  };
}
