/**
 * @fairfox/polly/test/contrast — WCAG contrast helpers for theme/dark-mode
 * tests (polly#141).
 *
 * Theme regressions are easy to ship and hard to catch, and hand-rolled checks
 * keep repeating the same mistakes: averaging RGB channels as a brightness
 * proxy (false passes for equal-luminance hues), reading a single
 * `backgroundColor` and skipping `rgba(0,0,0,0)` (silently dropping every
 * transparent-background element), and picking an arbitrary threshold. WCAG 2.1
 * has a defined answer — relative luminance, 4.5:1 for body text, 3:1 for UI
 * components and large text (SC 1.4.3 / 1.4.11) — and it belongs in one place.
 *
 * The pure functions (`parseColor`, `relativeLuminance`, `contrastRatio`) are
 * transport-agnostic: they work in Node and inside a Playwright/Puppeteer
 * `page.evaluate` bundle alike. `effectiveBackground` and `assertContrast` read
 * the live DOM and are meant for the harness side (or a `page.evaluate` where a
 * real `getComputedStyle` exists).
 */

import { CSS_NAMED_COLORS } from "./named-colors";

/** r, g, b in 0–255; a (alpha) in 0–1. */
export interface RGBA {
  r: number;
  g: number;
  b: number;
  a: number;
}

/** Anything `contrastRatio`/`assertContrast` will accept for a color. */
export type ColorInput = string | RGBA | { r: number; g: number; b: number };

const clamp = (n: number, lo: number, hi: number): number => Math.min(hi, Math.max(lo, n));
const clampChannel = (n: number): number => clamp(Math.round(n), 0, 255);

/** Parse one rgb/hsl numeric component that may be a percentage of `scale`. */
function parseComponent(token: string, scale: number): number {
  const t = token.trim();
  if (t.endsWith("%")) {
    return (Number.parseFloat(t) / 100) * scale;
  }
  return Number.parseFloat(t);
}

/** Parse an alpha token (`0.5` or `50%`) to 0–1. */
function parseAlpha(token: string | undefined): number {
  if (token === undefined) return 1;
  const t = token.trim();
  const value = t.endsWith("%") ? Number.parseFloat(t) / 100 : Number.parseFloat(t);
  return Number.isFinite(value) ? clamp(value, 0, 1) : 1;
}

function parseHex(input: string): RGBA | null {
  const hex = input.slice(1);
  const expand = (h: string): string =>
    h.length === 3 || h.length === 4
      ? h
          .split("")
          .map((c) => c + c)
          .join("")
      : h;
  const full = expand(hex);
  if (full.length !== 6 && full.length !== 8) return null;
  if (!/^[0-9a-fA-F]+$/.test(full)) return null;
  const r = Number.parseInt(full.slice(0, 2), 16);
  const g = Number.parseInt(full.slice(2, 4), 16);
  const b = Number.parseInt(full.slice(4, 6), 16);
  const a = full.length === 8 ? Number.parseInt(full.slice(6, 8), 16) / 255 : 1;
  return { r, g, b, a };
}

/** Split the inside of `fn(...)` into channel tokens and an optional alpha,
 * accepting both comma syntax (`r, g, b, a`) and modern slash syntax
 * (`r g b / a`). */
function splitFunctionArgs(inner: string): { parts: string[]; alpha: string | undefined } {
  const [head, alphaTail] = inner.split("/");
  const slashAlpha = alphaTail?.trim();
  const parts = (head ?? "")
    .trim()
    .split(/[\s,]+/)
    .filter(Boolean);
  if (slashAlpha !== undefined) {
    return { parts, alpha: slashAlpha };
  }
  // Comma syntax folds alpha into the 4th part.
  if (parts.length === 4) {
    return { parts: parts.slice(0, 3), alpha: parts[3] };
  }
  return { parts, alpha: undefined };
}

function parseRgb(inner: string): RGBA | null {
  const { parts, alpha } = splitFunctionArgs(inner);
  const [rToken, gToken, bToken] = parts;
  if (rToken === undefined || gToken === undefined || bToken === undefined) return null;
  const r = clampChannel(parseComponent(rToken, 255));
  const g = clampChannel(parseComponent(gToken, 255));
  const b = clampChannel(parseComponent(bToken, 255));
  if (![r, g, b].every(Number.isFinite)) return null;
  return { r, g, b, a: parseAlpha(alpha) };
}

/** HSL→RGB per CSS. h in degrees, s & l in 0–1. */
function hslToRgb(h: number, s: number, l: number): { r: number; g: number; b: number } {
  const hue = ((h % 360) + 360) % 360;
  const c = (1 - Math.abs(2 * l - 1)) * s;
  const x = c * (1 - Math.abs(((hue / 60) % 2) - 1));
  const m = l - c / 2;
  const [r1, g1, b1] = (() => {
    if (hue < 60) return [c, x, 0];
    if (hue < 120) return [x, c, 0];
    if (hue < 180) return [0, c, x];
    if (hue < 240) return [0, x, c];
    if (hue < 300) return [x, 0, c];
    return [c, 0, x];
  })();
  return {
    r: clampChannel((r1 + m) * 255),
    g: clampChannel((g1 + m) * 255),
    b: clampChannel((b1 + m) * 255),
  };
}

function parseHsl(inner: string): RGBA | null {
  const { parts, alpha } = splitFunctionArgs(inner);
  const [hToken, sToken, lToken] = parts;
  if (hToken === undefined || sToken === undefined || lToken === undefined) return null;
  const h = Number.parseFloat(hToken.replace(/deg$/, ""));
  const s = clamp(parseComponent(sToken, 100) / 100, 0, 1);
  const l = clamp(parseComponent(lToken, 100) / 100, 0, 1);
  if (![h, s, l].every(Number.isFinite)) return null;
  return { ...hslToRgb(h, s, l), a: parseAlpha(alpha) };
}

/**
 * Parse a CSS color string to `{ r, g, b, a }`, or `null` if unrecognised.
 * Handles `#rgb`, `#rgba`, `#rrggbb`, `#rrggbbaa`, `rgb()/rgba()` (comma or
 * space syntax, with optional `/ alpha`), `hsl()/hsla()`, `transparent`, and
 * the full set of CSS named colors. This is the parse `getComputedStyle`
 * output needs (always `rgb()`/`rgba()`) plus the literal forms a test author
 * is likely to pass to `against`.
 */
export function parseColor(input: string): RGBA | null {
  if (typeof input !== "string") return null;
  const value = input.trim();
  if (value === "") return null;
  const lower = value.toLowerCase();

  if (lower === "transparent") return { r: 0, g: 0, b: 0, a: 0 };

  const named = CSS_NAMED_COLORS[lower];
  if (named) return parseHex(named);

  if (value.startsWith("#")) return parseHex(value);

  const fn = value.match(/^([a-z]+)\(([^)]*)\)$/i);
  const [, fnName, fnInner] = fn ?? [];
  if (fnName !== undefined && fnInner !== undefined) {
    const name = fnName.toLowerCase();
    if (name === "rgb" || name === "rgba") return parseRgb(fnInner);
    if (name === "hsl" || name === "hsla") return parseHsl(fnInner);
  }
  return null;
}

/** Coerce a ColorInput to RGBA (assuming alpha 1 when absent), or null. */
function toRGBA(input: ColorInput): RGBA | null {
  if (typeof input === "string") return parseColor(input);
  if (input && typeof input === "object" && "r" in input) {
    return { r: input.r, g: input.g, b: input.b, a: "a" in input ? input.a : 1 };
  }
  return null;
}

/**
 * WCAG relative luminance (0–1) of an opaque color. Alpha is ignored — composite
 * first (see `compositeOver`) if the color is translucent.
 */
export function relativeLuminance(color: { r: number; g: number; b: number }): number {
  const channel = (c: number): number => {
    const cs = c / 255;
    return cs <= 0.03928 ? cs / 12.92 : ((cs + 0.055) / 1.055) ** 2.4;
  };
  return 0.2126 * channel(color.r) + 0.7152 * channel(color.g) + 0.0722 * channel(color.b);
}

/**
 * WCAG contrast ratio (1–21) between two colors. Accepts CSS strings or RGB(A)
 * objects. Alpha is ignored; composite translucent colors over their background
 * first. Returns `NaN` if either input cannot be parsed.
 */
export function contrastRatio(a: ColorInput, b: ColorInput): number {
  const ca = toRGBA(a);
  const cb = toRGBA(b);
  if (!ca || !cb) return Number.NaN;
  const la = relativeLuminance(ca);
  const lb = relativeLuminance(cb);
  const lighter = Math.max(la, lb);
  const darker = Math.min(la, lb);
  return (lighter + 0.05) / (darker + 0.05);
}

/**
 * Alpha-composite `fg` over `bg` (the "over" operator), returning an opaque
 * color. `bg` is assumed opaque (its alpha is treated as 1).
 */
export function compositeOver(fg: RGBA, bg: RGBA): RGBA {
  const a = clamp(fg.a, 0, 1);
  return {
    r: clampChannel(fg.r * a + bg.r * (1 - a)),
    g: clampChannel(fg.g * a + bg.g * (1 - a)),
    b: clampChannel(fg.b * a + bg.b * (1 - a)),
    a: 1,
  };
}

/**
 * Resolve the effective (opaque) background an element renders against by
 * walking up the ancestor chain, compositing each translucent background over
 * the next, until an opaque one is reached. Elements with a fully transparent
 * background — most of them — are no longer silently skipped: they contribute
 * their (zero) alpha and the walk continues to the parent. Falls back to white
 * when the chain reaches the root without an opaque background.
 */
export function effectiveBackground(element: Element): RGBA {
  const view = element.ownerDocument?.defaultView;
  const getStyle = view?.getComputedStyle?.bind(view);
  const stack: RGBA[] = [];

  let node: Element | null = element;
  while (node && getStyle) {
    const parsed = parseColor(getStyle(node).backgroundColor || "");
    if (parsed && parsed.a > 0) {
      stack.push(parsed);
      if (parsed.a >= 1) break;
    }
    node = node.parentElement;
  }

  // Composite from the deepest opaque layer outward toward the element.
  let result: RGBA = { r: 255, g: 255, b: 255, a: 1 };
  for (let i = stack.length - 1; i >= 0; i--) {
    const layer = stack[i];
    if (layer === undefined) continue;
    result = compositeOver(layer, result);
  }
  return result;
}

export interface AssertContrastOptions {
  /** Minimum acceptable ratio. WCAG: 3 (UI/large text), 4.5 (body), 7 (AAA). */
  min: 3 | 4.5 | 7 | number;
  /**
   * Background to measure against. `"effective"` (default) walks the ancestor
   * chain via `effectiveBackground`; an explicit color (string or RGB) skips
   * the walk.
   */
  against?: "effective" | ColorInput;
}

export interface ContrastResult {
  ratio: number;
  foreground: RGBA;
  background: RGBA;
  min: number;
  passes: boolean;
}

function describeElement(element: Element): string {
  const tag = element.tagName.toLowerCase();
  const id = element.id ? `#${element.id}` : "";
  const cls = element.getAttribute("class");
  const classes = cls ? `.${cls.trim().split(/\s+/).join(".")}` : "";
  return `${tag}${id}${classes}`;
}

const fmt = (c: RGBA): string =>
  c.a >= 1 ? `rgb(${c.r}, ${c.g}, ${c.b})` : `rgba(${c.r}, ${c.g}, ${c.b}, ${c.a})`;

/**
 * Assert an element's text meets a WCAG contrast minimum against its
 * background, throwing a message that names the element, both colors, and the
 * actual ratio. The element's own (possibly translucent) text color is
 * composited over the resolved background before measuring. Returns the
 * computed `ContrastResult` on success so callers can log or assert further.
 */
export function assertContrast(element: Element, options: AssertContrastOptions): ContrastResult {
  const view = element.ownerDocument?.defaultView;
  const getStyle = view?.getComputedStyle?.bind(view);
  if (!getStyle) {
    throw new Error("assertContrast: no getComputedStyle available on the element's document");
  }

  const fgRaw = parseColor(getStyle(element).color || "");
  if (!fgRaw) {
    throw new Error(`assertContrast: could not parse the color of ${describeElement(element)}`);
  }

  const against = options.against ?? "effective";
  const background = against === "effective" ? effectiveBackground(element) : toRGBA(against);
  if (!background) {
    throw new Error(
      `assertContrast: could not parse the 'against' color for ${describeElement(element)}`
    );
  }

  const foreground = fgRaw.a < 1 ? compositeOver(fgRaw, background) : fgRaw;
  const ratio = contrastRatio(foreground, background);
  const passes = ratio >= options.min;

  if (!passes) {
    throw new Error(
      `Contrast ${ratio.toFixed(2)}:1 is below the required ${options.min}:1 for ` +
        `${describeElement(element)} — foreground ${fmt(foreground)} on background ${fmt(background)}.`
    );
  }

  return { ratio, foreground, background, min: options.min, passes };
}
