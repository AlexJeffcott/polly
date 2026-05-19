/**
 * Surface — the one primitive that owns visual-surface concerns.
 *
 * Where Layout governs spatial concerns (grid, flex, gap, alignment),
 * Surface governs the chrome that sits on top of layout: padding,
 * background, border, radius, shadow, and the narrow positioning idioms
 * (sticky strips, fixed floating panes) that consumers reach for inline
 * styles to express. Every prop maps to a `--polly-*` token through a
 * local `--s-*` custom property, so consumers can retheme an individual
 * Surface by overriding the polly token in `style` without touching the
 * primitive's CSS.
 */

import { type ComponentChildren, createElement, type JSX } from "preact";
import classes from "./Surface.module.css";

export type SurfaceVariant =
  | "plain"
  | "raised"
  | "sunken"
  | "bubble"
  | "chip"
  | "callout"
  | "floating"
  | "sticky-bar";

type Background = "raised" | "sunken" | "transparent" | (string & {});
type Radius = "none" | "sm" | "md" | "lg" | "full";
type Border = "none" | "default" | "strong";
type BorderWidth = "none" | "default" | "medium" | "thick";
type BorderSides =
  | "all"
  | "block-start"
  | "block-end"
  | "inline-start"
  | "inline-end"
  | "block"
  | "inline";
type Shadow = "none" | "sm" | "md" | "lg";
type Position = "static" | "relative" | "sticky" | "fixed";

/**
 * Arbitrary `data-*` and `aria-*` attributes forwarded to the rendered element
 * so consumers (Modal, Toast, Card, etc.) can compose Surface without losing
 * DOM hooks or ARIA semantics.
 */
export type SurfaceDataAttrs = {
  [dataAttr: `data-${string}`]: string | number | boolean | undefined;
  [ariaAttr: `aria-${string}`]: string | number | boolean | undefined;
};

export type SurfaceProps = SurfaceDataAttrs & {
  children?: ComponentChildren;

  /** Polymorphic element (div, section, article, aside, header, …). Defaults to 'div'. */
  as?: keyof JSX.IntrinsicElements;

  /** Named preset that resolves to a default bundle of the props below. Explicit props override. */
  variant?: SurfaceVariant;

  /** Any CSS length, typically `var(--polly-space-*)`. */
  padding?: string;

  /** Named values map to `var(--polly-surface-*)`; raw strings pass through for one-off colours. */
  background?: Background;

  radius?: Radius;
  border?: Border;
  borderWidth?: BorderWidth;
  borderSides?: BorderSides;
  shadow?: Shadow;

  /** display: inline-block — Surface flows inline with surrounding text. */
  inline?: boolean;
  width?: string;
  height?: string;
  minHeight?: string;
  maxInlineSize?: string;

  position?: Position;
  /** Any CSS inset value (`'0'`, `'auto auto 1rem 1rem'`, `'1rem'`, …). */
  inset?: string;
  zIndex?: number;

  className?: string;
  /**
   * Per-instance overrides. The supported retint path is to set polly tokens
   * here, e.g. `style={{ "--polly-surface-raised": "#fef3c7" }}`. Surface
   * merges this into its own computed style.
   */
  style?: JSX.CSSProperties;

  id?: string;
  role?: JSX.AriaRole;
  tabIndex?: number;
  "aria-label"?: string;
  "aria-labelledby"?: string;
  "aria-describedby"?: string;
  onClick?: JSX.MouseEventHandler<HTMLElement>;
  onKeyDown?: JSX.KeyboardEventHandler<HTMLElement>;
};

type VariantDefaults = Partial<
  Pick<
    SurfaceProps,
    | "padding"
    | "background"
    | "radius"
    | "border"
    | "borderWidth"
    | "borderSides"
    | "shadow"
    | "inline"
    | "width"
    | "height"
    | "minHeight"
    | "maxInlineSize"
    | "position"
    | "inset"
    | "zIndex"
  >
>;

const variantDefaults: Record<SurfaceVariant, VariantDefaults> = {
  plain: {},
  raised: {
    background: "raised",
    radius: "md",
    shadow: "md",
    border: "default",
  },
  sunken: {
    background: "sunken",
    radius: "md",
    border: "default",
  },
  bubble: {
    radius: "md",
    border: "default",
    padding: "var(--polly-space-sm) var(--polly-space-md)",
  },
  chip: {
    inline: true,
    radius: "full",
    padding: "var(--polly-space-xs) var(--polly-space-sm)",
    border: "default",
  },
  callout: {
    border: "default",
    radius: "sm",
    padding: "var(--polly-space-sm) var(--polly-space-md)",
  },
  floating: {
    position: "fixed",
    radius: "lg",
    shadow: "lg",
    border: "default",
    background: "raised",
    zIndex: 9999,
  },
  "sticky-bar": {
    position: "sticky",
    inset: "0 0 auto 0",
    borderSides: "block-end",
    border: "default",
  },
};

function bgValue(b: Background): string {
  if (b === "raised") return "var(--polly-surface-raised)";
  if (b === "sunken") return "var(--polly-surface-sunken)";
  if (b === "transparent") return "transparent";
  return b;
}

function radiusValue(r: Radius): string {
  if (r === "none") return "0";
  return `var(--polly-radius-${r})`;
}

function borderColorValue(b: Border): string {
  if (b === "none") return "transparent";
  if (b === "strong") return "var(--polly-border-strong)";
  return "var(--polly-border)";
}

function borderWidthValue(w: BorderWidth): string {
  if (w === "none") return "0";
  return `var(--polly-border-width-${w})`;
}

function shadowValue(s: Shadow): string {
  if (s === "none") return "none";
  return `var(--polly-shadow-${s})`;
}

function borderSidesClass(sides: BorderSides): string | undefined {
  if (sides === "all") return undefined;
  if (sides === "block-start") return classes["sides-block-start"];
  if (sides === "block-end") return classes["sides-block-end"];
  if (sides === "inline-start") return classes["sides-inline-start"];
  if (sides === "inline-end") return classes["sides-inline-end"];
  if (sides === "block") return classes["sides-block"];
  if (sides === "inline") return classes["sides-inline"];
  return undefined;
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: prop-to-custom-property mapping; flat and linear, mirrors Layout.tsx.
export function Surface(props: SurfaceProps): JSX.Element {
  const { variant = "plain" } = props;
  const v = variantDefaults[variant];

  const as = props.as ?? "div";
  const padding = props.padding ?? v.padding;
  const background = props.background ?? v.background;
  const radius = props.radius ?? v.radius;
  const border = props.border ?? v.border;
  const borderSides = props.borderSides ?? v.borderSides ?? "all";
  const shadow = props.shadow ?? v.shadow;
  const inline = props.inline ?? v.inline;
  const width = props.width ?? v.width;
  const height = props.height ?? v.height;
  const minHeight = props.minHeight ?? v.minHeight;
  const maxInlineSize = props.maxInlineSize ?? v.maxInlineSize;
  const position = props.position ?? v.position;
  const inset = props.inset ?? v.inset;
  const zIndex = props.zIndex ?? v.zIndex;

  // A bordered surface needs a width. If the consumer asked for a border but
  // didn't pick a width, infer 'default' so the border renders.
  const borderWidth =
    props.borderWidth ?? v.borderWidth ?? (border && border !== "none" ? "default" : undefined);

  const style: Record<string, string> = {};
  if (padding) style["--s-p"] = padding;
  if (background) style["--s-bg"] = bgValue(background);
  if (radius) style["--s-radius"] = radiusValue(radius);
  if (border) style["--s-border-color"] = borderColorValue(border);
  if (borderWidth) style["--s-border-width"] = borderWidthValue(borderWidth);
  if (shadow) style["--s-shadow"] = shadowValue(shadow);
  if (width) style["--s-w"] = width;
  if (height) style["--s-h"] = height;
  if (minHeight) style["--s-mh"] = minHeight;
  if (maxInlineSize) style["--s-mis"] = maxInlineSize;
  if (position) style["--s-position"] = position;
  if (inset) style["--s-inset"] = inset;
  if (zIndex !== undefined) style["--s-z"] = String(zIndex);

  if (props.style) {
    Object.assign(style, props.style as unknown as Record<string, string>);
  }

  const parts: (string | undefined)[] = [classes["surface"]];
  if (inline) parts.push(classes["inline"]);
  parts.push(borderSidesClass(borderSides));
  if (props.className) parts.push(props.className);
  const className = parts.filter(Boolean).join(" ");

  const passthrough: Record<string, string | number | boolean> = {};
  for (const key of Object.keys(props)) {
    const isData = key.startsWith("data-");
    const isAria = key.startsWith("aria-");
    if (!isData && !isAria) continue;
    if (key === "data-polly-surface") continue;
    if (key === "aria-label" || key === "aria-labelledby" || key === "aria-describedby") continue;
    const value = (props as unknown as Record<string, unknown>)[key];
    if (value === undefined) continue;
    if (typeof value === "string" || typeof value === "number" || typeof value === "boolean") {
      passthrough[key] = value;
    }
  }

  return createElement(
    as,
    {
      id: props.id,
      className,
      style,
      onClick: props.onClick,
      onKeyDown: props.onKeyDown,
      role: props.role,
      tabIndex: props.tabIndex,
      "aria-label": props["aria-label"],
      "aria-labelledby": props["aria-labelledby"],
      "aria-describedby": props["aria-describedby"],
      "data-polly-surface": variant,
      ...passthrough,
    },
    props.children
  );
}
