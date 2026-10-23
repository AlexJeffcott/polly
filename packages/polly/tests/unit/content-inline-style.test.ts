import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";
import { inlineStyleOf } from "@/content/inline-style";

beforeAll(() => {
  GlobalRegistrator.register();
});

afterAll(async () => {
  await GlobalRegistrator.unregister();
});

describe("inlineStyleOf", () => {
  test("returns the inline style of an HTML element", () => {
    const el = document.createElement("div");
    const style = inlineStyleOf(el);
    expect(style).toBe(el.style);
  });

  test("returns the inline style of an SVG element", () => {
    const el = document.createElementNS("http://www.w3.org/2000/svg", "rect");
    expect(inlineStyleOf(el)).toBeInstanceOf(CSSStyleDeclaration);
  });

  test("returns undefined for an element with no style", () => {
    const el = document.createElementNS("urn:example", "x:item");
    expect("style" in el).toBe(false);
    expect(inlineStyleOf(el)).toBeUndefined();
  });
});
