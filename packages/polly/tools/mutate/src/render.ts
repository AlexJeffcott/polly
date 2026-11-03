/**
 * Render a `MutationConfig` as the `polly.mutate.ts` source `polly mutate init`
 * writes.
 */
import { existsSync } from "node:fs";
import { join, relative } from "node:path";
import type { MutationConfig } from "./define.ts";

/**
 * The specifier a config in `dir` imports `defineMutation` from: the package
 * export when it resolves there, else this source tree's own module (polly's
 * monorepo root has no `@fairfox/polly` in its node_modules).
 */
export function defineImportSpecifier(dir: string): string {
  try {
    Bun.resolveSync("@fairfox/polly/mutate", dir);
    return "@fairfox/polly/mutate";
  } catch {
    const local = join(import.meta.dir, "define.ts");
    if (!existsSync(local)) return "@fairfox/polly/mutate";
    const rel = relative(dir, local);
    return rel.startsWith(".") ? rel : `./${rel}`;
  }
}

/** Biome's default line width; a longer line is left one-element-per-line. */
const LINE_WIDTH = 100;

/**
 * Render a value as a TypeScript object literal in the shape biome's formatter
 * produces: unquoted keys, trailing commas, and an array of primitives on one
 * line when it fits in LINE_WIDTH, so `polly mutate init` passes `polly lint`.
 */
function literal(value: unknown): string {
  return JSON.stringify(value, null, 2)
    .replace(/^(\s*)"([A-Za-z_$][\w$]*)":/gm, "$1$2:")
    .replace(/([^\s[{,])(?=\n\s*[}\]])/g, "$1,")
    .replace(
      /^([ ]*)([\w$]+: )?\[\n((?:[ ]*(?:"[^"\n]*"|-?\d+(?:\.\d+)?|true|false),\n)+)([ ]*)\](,?)$/gm,
      (m, indent, key, items, _close, comma) => {
        const inline = `${indent}${key ?? ""}[${items
          .trim()
          .replace(/,$/, "")
          .split(/,\n\s*/)
          .join(", ")}]${comma}`;
        return inline.length <= LINE_WIDTH ? inline : m;
      }
    );
}

export function renderMutationConfig(config: MutationConfig, specifier: string): string {
  return [
    `import { defineMutation } from "${specifier}";`,
    "",
    `export default defineMutation(${literal(config)});`,
    "",
  ].join("\n");
}
