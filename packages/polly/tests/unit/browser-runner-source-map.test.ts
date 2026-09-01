/**
 * Tests for the browser runner's source-map lookup (polly#177).
 *
 * When a page wedges, the runner pauses it and prints the frames it was
 * running. Without this lookup those frames name a line of the generated
 * bundle, which tells the author nothing about their own code — the same
 * unhelpful silence the issue started from. The lookup has to survive a real
 * Bun.build bundle, a wrapper offset, and a bundle with no map at all.
 */

import { describe, expect, test } from "bun:test";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  createSourceMapLookup,
  parseInlineSourceMap,
} from "../../tools/test/src/browser/source-map";

/** A hand-built map: generated line 0 comes from `a.ts`, line 1 from `b.ts`. */
function fixtureBundle(lineOffset = 0): string {
  const map = {
    version: 3,
    sources: ["a.ts", "b.ts"],
    // ;-separated generated lines. Segment fields are
    // [generatedColumn, sourceIndex, sourceLine, sourceColumn] as VLQ deltas.
    // "AAAA" is all-zero; "ACAA" advances the source index by 1.
    // "IAAI" advances the generated and source columns by 4. Source line and
    // column are running deltas across the whole map, not per line, so the
    // segment on generated line 1 inherits source column 4.
    mappings: "AAAA,IAAI;ACAA",
  };
  const encoded = Buffer.from(JSON.stringify(map), "utf8").toString("base64");
  return `${"\n".repeat(lineOffset)}generated line one\ngenerated line two\n//# sourceMappingURL=data:application/json;base64,${encoded}`;
}

describe("parseInlineSourceMap", () => {
  test("reads a bundle's inline map", () => {
    const map = parseInlineSourceMap(fixtureBundle());

    expect(map?.sources).toEqual(["a.ts", "b.ts"]);
  });

  test("returns undefined for a bundle with no map", () => {
    expect(parseInlineSourceMap("just some code\n")).toBeUndefined();
  });

  test("returns undefined rather than throwing on a corrupt map", () => {
    const bundle = "code\n//# sourceMappingURL=data:application/json;base64,bm90IGpzb24=";

    expect(parseInlineSourceMap(bundle)).toBeUndefined();
  });
});

describe("createSourceMapLookup", () => {
  test("resolves a generated position to its original source", () => {
    const lookup = createSourceMapLookup(fixtureBundle());

    expect(lookup?.(0, 0)).toBe("a.ts:1:0");
    expect(lookup?.(1, 0)).toBe("b.ts:1:4");
  });

  test("picks the last segment at or before the column", () => {
    const lookup = createSourceMapLookup(fixtureBundle());

    // Column 4 starts a second segment on generated line 0.
    expect(lookup?.(0, 0)).toBe("a.ts:1:0");
    expect(lookup?.(0, 9)).toBe("a.ts:1:4");
  });

  test("subtracts the wrapper's line offset", () => {
    // Three lines of wrapper above the bundle, as the served document has.
    const lookup = createSourceMapLookup(fixtureBundle(3), 3);

    expect(lookup?.(3, 0)).toBe("a.ts:1:0");
    expect(lookup?.(4, 0)).toBe("b.ts:1:4");
  });

  test("returns undefined above the wrapper and past the end", () => {
    const lookup = createSourceMapLookup(fixtureBundle(3), 3);

    expect(lookup?.(1, 0)).toBeUndefined();
    expect(lookup?.(99, 0)).toBeUndefined();
  });

  test("returns undefined when the bundle carries no map", () => {
    expect(createSourceMapLookup("plain code")).toBeUndefined();
  });

  test("resolves a position in a real Bun.build bundle back to the source file", async () => {
    const dir = await mkdtemp(join(tmpdir(), "polly-source-map-"));
    try {
      const entry = join(dir, "entry.ts");
      await writeFile(
        entry,
        ["export function first() {", "  return 1;", "}", "", "export const marker = 42;", ""].join(
          "\n"
        ),
        "utf8"
      );
      const build = await Bun.build({
        entrypoints: [entry],
        target: "browser",
        format: "esm",
        sourcemap: "inline",
      });
      expect(build.success).toBe(true);
      const jsText = (await build.outputs[0]?.text()) ?? "";

      const lookup = createSourceMapLookup(jsText);
      expect(lookup).toBeDefined();

      // Find the generated line holding the function body and map it back.
      const lines = jsText.split("\n");
      const generatedLine = lines.findIndex((l) => l.includes("return 1;"));
      expect(generatedLine).toBeGreaterThan(-1);
      const resolved = lookup?.(generatedLine, lines[generatedLine]?.indexOf("return") ?? 0);

      expect(resolved).toContain("entry.ts");
      // `return 1;` is the second line of the source file.
      expect(resolved?.endsWith(":2:2")).toBe(true);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
