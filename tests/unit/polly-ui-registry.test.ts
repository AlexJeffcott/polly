import { describe, expect, test } from "bun:test";
import { pollyUiComponents, pollyUiTokens } from "../../src/polly-ui/registry";

describe("polly-ui registry", () => {
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

  test("every token name starts with `polly-`", () => {
    for (const t of pollyUiTokens) {
      expect(t.name.startsWith("polly-")).toBe(true);
    }
  });
});
