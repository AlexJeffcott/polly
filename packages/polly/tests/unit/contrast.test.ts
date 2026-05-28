/**
 * Tests for the WCAG contrast helpers (polly#141).
 *
 * The pure functions (parse / luminance / ratio / composite) are validated
 * against known WCAG values and the specific traps the issue calls out — the
 * channel-average false-pass and the transparent-background false-skip. The DOM
 * helpers (effectiveBackground / assertContrast) run against happy-dom.
 */

import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";
import {
  assertContrast,
  compositeOver,
  contrastRatio,
  effectiveBackground,
  parseColor,
  relativeLuminance,
} from "../../tools/test/src/contrast/index";

describe("parseColor", () => {
  test("hex in 3/4/6/8 digit forms", () => {
    expect(parseColor("#fff")).toEqual({ r: 255, g: 255, b: 255, a: 1 });
    expect(parseColor("#000000")).toEqual({ r: 0, g: 0, b: 0, a: 1 });
    expect(parseColor("#ff000080")).toEqual({ r: 255, g: 0, b: 0, a: 128 / 255 });
    expect(parseColor("#f008")).toEqual({ r: 255, g: 0, b: 0, a: 136 / 255 });
  });

  test("rgb / rgba in comma, space, and slash syntax", () => {
    expect(parseColor("rgb(18, 52, 86)")).toEqual({ r: 18, g: 52, b: 86, a: 1 });
    expect(parseColor("rgba(18, 52, 86, 0.5)")).toEqual({ r: 18, g: 52, b: 86, a: 0.5 });
    expect(parseColor("rgb(18 52 86)")).toEqual({ r: 18, g: 52, b: 86, a: 1 });
    expect(parseColor("rgb(18 52 86 / 0.25)")).toEqual({ r: 18, g: 52, b: 86, a: 0.25 });
  });

  test("hsl resolves to the right rgb", () => {
    expect(parseColor("hsl(0, 100%, 50%)")).toEqual({ r: 255, g: 0, b: 0, a: 1 });
    expect(parseColor("hsl(120 100% 50%)")).toEqual({ r: 0, g: 255, b: 0, a: 1 });
    expect(parseColor("hsla(240, 100%, 50%, 0.5)")).toEqual({ r: 0, g: 0, b: 255, a: 0.5 });
  });

  test("transparent and named colors", () => {
    expect(parseColor("transparent")).toEqual({ r: 0, g: 0, b: 0, a: 0 });
    expect(parseColor("white")).toEqual({ r: 255, g: 255, b: 255, a: 1 });
    expect(parseColor("REBECCAPURPLE")).toEqual({ r: 102, g: 51, b: 153, a: 1 });
    expect(parseColor("tomato")).toEqual({ r: 255, g: 99, b: 71, a: 1 });
  });

  test("returns null for unrecognised input", () => {
    expect(parseColor("not-a-color")).toBeNull();
    expect(parseColor("")).toBeNull();
    expect(parseColor("#xyz")).toBeNull();
  });
});

describe("relativeLuminance / contrastRatio", () => {
  test("black on white is the maximal 21:1", () => {
    expect(relativeLuminance({ r: 255, g: 255, b: 255 })).toBeCloseTo(1, 5);
    expect(relativeLuminance({ r: 0, g: 0, b: 0 })).toBeCloseTo(0, 5);
    expect(contrastRatio("#000", "#fff")).toBeCloseTo(21, 5);
  });

  test("identical colors are 1:1", () => {
    expect(contrastRatio("#777", "#777")).toBeCloseTo(1, 5);
  });

  test("equal-luminance-average hues are NOT 1:1 (the channel-average trap)", () => {
    // rgb(0,200,0) vs rgb(200,0,0): channel averages are equal (both ~66.7),
    // so an average-based check reports 0 difference. Real luminance differs.
    const ratio = contrastRatio("rgb(0, 200, 0)", "rgb(200, 0, 0)");
    expect(ratio).toBeGreaterThan(2);
    expect(ratio).not.toBeCloseTo(1, 1);
  });

  test("unparseable input yields NaN rather than a misleading number", () => {
    expect(contrastRatio("garbage", "#fff")).toBeNaN();
  });
});

describe("compositeOver", () => {
  test("50% red over white blends to a pink", () => {
    expect(compositeOver({ r: 255, g: 0, b: 0, a: 0.5 }, { r: 255, g: 255, b: 255, a: 1 })).toEqual(
      {
        r: 255,
        g: 128,
        b: 128,
        a: 1,
      }
    );
  });

  test("a fully transparent foreground leaves the background", () => {
    expect(compositeOver({ r: 0, g: 0, b: 0, a: 0 }, { r: 10, g: 20, b: 30, a: 1 })).toEqual({
      r: 10,
      g: 20,
      b: 30,
      a: 1,
    });
  });
});

describe("DOM helpers (happy-dom)", () => {
  beforeAll(() => {
    GlobalRegistrator.register();
  });
  afterAll(async () => {
    await GlobalRegistrator.unregister();
  });

  test("effectiveBackground walks past a transparent child to the painted ancestor", () => {
    document.body.innerHTML = "";
    const parent = document.createElement("div");
    parent.style.backgroundColor = "rgb(10, 20, 30)";
    const child = document.createElement("span"); // no background → transparent
    parent.appendChild(child);
    document.body.appendChild(parent);

    expect(effectiveBackground(child)).toEqual({ r: 10, g: 20, b: 30, a: 1 });
  });

  test("effectiveBackground composites a translucent layer over its ancestor", () => {
    document.body.innerHTML = "";
    const parent = document.createElement("div");
    parent.style.backgroundColor = "rgb(0, 0, 0)";
    const child = document.createElement("div");
    child.style.backgroundColor = "rgba(255, 255, 255, 0.5)";
    parent.appendChild(child);
    document.body.appendChild(parent);

    // White at 50% over black → mid grey.
    expect(effectiveBackground(child)).toEqual({ r: 128, g: 128, b: 128, a: 1 });
  });

  test("assertContrast passes for black text on white and returns the ratio", () => {
    document.body.innerHTML = "";
    const el = document.createElement("p");
    el.style.color = "rgb(0, 0, 0)";
    el.style.backgroundColor = "rgb(255, 255, 255)";
    document.body.appendChild(el);

    const result = assertContrast(el, { min: 4.5 });
    expect(result.passes).toBe(true);
    expect(result.ratio).toBeCloseTo(21, 5);
  });

  test("assertContrast throws a descriptive error when below the minimum", () => {
    document.body.innerHTML = "";
    const el = document.createElement("button");
    el.className = "ghost danger";
    el.style.color = "rgb(200, 200, 200)";
    el.style.backgroundColor = "rgb(255, 255, 255)";
    document.body.appendChild(el);

    expect(() => assertContrast(el, { min: 4.5 })).toThrow(/below the required 4\.5:1/);
    expect(() => assertContrast(el, { min: 4.5 })).toThrow(/button\.ghost\.danger/);
  });

  test("assertContrast honours an explicit against color", () => {
    document.body.innerHTML = "";
    const el = document.createElement("span");
    el.style.color = "rgb(255, 255, 255)";
    document.body.appendChild(el);

    // White on white fails; white on black passes — proves `against` is used.
    expect(() => assertContrast(el, { min: 3, against: "white" })).toThrow();
    expect(assertContrast(el, { min: 3, against: "black" }).ratio).toBeCloseTo(21, 5);
  });
});
