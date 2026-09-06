import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { pollyUiComponents, pollyUiTokens } from "../../src/polly-ui/registry";

const INDEX_PATH = join(import.meta.dir, "../../src/polly-ui/index.ts");

/**
 * The components `index.ts` actually exports: every member of an
 * `export { … } from "./X.tsx"` block that is a value (no `type` prefix) and
 * starts with a capital. Read here from the source of truth rather than from
 * the generator, so the two can disagree and this test can say so.
 */
function exportedComponentNames(): string[] {
  const source = readFileSync(INDEX_PATH, "utf8");
  const names = new Set<string>();
  for (const block of source.matchAll(/export\s*\{([^}]*)\}\s*from\s*"\.\/[^"]+"/g)) {
    for (const member of (block[1] ?? "").split(",")) {
      const token = member.trim();
      if (token.length === 0 || /^type\s/.test(token)) continue;
      const parts = token.split(/\s+as\s+/);
      const name = (parts[parts.length - 1] ?? "").trim();
      if (/^[A-Z]\w*$/.test(name)) names.add(name);
    }
  }
  return [...names].sort();
}

describe("polly-ui registry", () => {
  // The generator used to read only the FIRST member of each export brace, so
  // biome's alphabetical sort silently cost it any component whose brace led
  // with a `type` keyword (`export { type Tab, Tabs, … }`) or a lowercase
  // helper (`export { getOverlayRootNode, OverlayRoot }`). Tabs and OverlayRoot
  // were missing from the registry for the life of the library and no test
  // said so, because every test asked the registry about itself. This one asks
  // index.ts.
  test("the registry covers every component index.ts exports", () => {
    const exported = exportedComponentNames();
    const registered = pollyUiComponents.map((c) => c.name).sort();
    expect(exported.length).toBeGreaterThan(0);
    expect(registered).toEqual(exported);
  });

  test("the registry lists no component index.ts does not export", () => {
    const exported = new Set(exportedComponentNames());
    const strays = pollyUiComponents.map((c) => c.name).filter((n) => !exported.has(n));
    expect(strays).toEqual([]);
  });

  test("lowercase helper exports are not components", () => {
    const names = new Set(pollyUiComponents.map((c) => c.name));
    // Both are real exports of index.ts and neither is a component.
    expect(names.has("confirm")).toBe(false);
    expect(names.has("getOverlayRootNode")).toBe(false);
  });

  test("exposes the expected core token categories", () => {
    const categories = new Set<string>(pollyUiTokens.map((t) => t.category));
    for (const expected of ["color", "spacing", "radius", "sizing"]) {
      expect(categories.has(expected)).toBe(true);
    }
  });

  test("every token has a non-empty default value", () => {
    for (const t of pollyUiTokens) {
      expect(t.default.length).toBeGreaterThan(0);
    }
  });

  test("contains the canonical accent and surface tokens", () => {
    const names = new Set(pollyUiTokens.map((t) => t.name));
    expect(names.has("polly-accent")).toBe(true);
    expect(names.has("polly-surface")).toBe(true);
    expect(names.has("polly-text")).toBe(true);
  });

  test("Button component is registered with `button` as a replacement", () => {
    const btn = pollyUiComponents.find((c) => c.name === "Button");
    expect(btn).toBeDefined();
    expect(btn?.replaces).toContain("button");
    expect(btn?.importPath).toBe("@fairfox/polly/ui");
  });

  test("Modal replaces dialog, ActionForm replaces form", () => {
    const modal = pollyUiComponents.find((c) => c.name === "Modal");
    expect(modal?.replaces).toContain("dialog");
    const form = pollyUiComponents.find((c) => c.name === "ActionForm");
    expect(form?.replaces).toContain("form");
  });

  test("registers the issue-123 primitives (Text, Cluster, Code, ActionSelect)", () => {
    const names = new Set(pollyUiComponents.map((c) => c.name));
    expect(names.has("Text")).toBe(true);
    expect(names.has("Cluster")).toBe(true);
    expect(names.has("Code")).toBe(true);
    expect(names.has("ActionSelect")).toBe(true);
  });

  test("ActionSelect and Select both replace the native select element", () => {
    const select = pollyUiComponents.find((c) => c.name === "Select");
    const actionSelect = pollyUiComponents.find((c) => c.name === "ActionSelect");
    expect(select?.replaces).toContain("select");
    expect(actionSelect?.replaces).toContain("select");
  });

  test("every token name starts with `polly-`", () => {
    for (const t of pollyUiTokens) {
      expect(t.name.startsWith("polly-")).toBe(true);
    }
  });
});
