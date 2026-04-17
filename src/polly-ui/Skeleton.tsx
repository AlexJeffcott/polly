/**
 * Skeleton — shimmering placeholder for loading states.
 *
 * Three variants: text (full-width, 1em tall), rect (full-width, 100px
 * tall), circle (40x40). A CSS gradient animates left-to-right over
 * 1.5s. `prefers-reduced-motion` zeroes the animation via the token
 * system. Consumers size via width/height props (px numbers or CSS
 * strings); default sizing comes from the variant.
 */

import type { JSX } from "preact";
import classes from "./Skeleton.module.css";

export type SkeletonVariant = "text" | "rect" | "circle";

export type SkeletonProps = {
  variant?: SkeletonVariant;
  width?: string | number;
  height?: string | number;
  className?: string;
};

function resolveSize(value: string | number | undefined): string | undefined {
  if (value === undefined) return undefined;
  if (typeof value === "number") return `${value}px`;
  return value;
}

function variantClass(variant: SkeletonVariant): string | undefined {
  if (variant === "circle") return classes["circle"];
  if (variant === "rect") return classes["rect"];
  return classes["text"];
}

export function Skeleton(props: SkeletonProps): JSX.Element {
  const { variant = "text", width, height, className } = props;

  const style: Record<string, string> = {};
  const w = resolveSize(width);
  const h = resolveSize(height);
  if (w !== undefined) style["width"] = w;
  if (h !== undefined) style["height"] = h;

  const parts: string[] = [];
  const base = classes["skeleton"];
  if (base) parts.push(base);
  const vClass = variantClass(variant);
  if (vClass) parts.push(vClass);
  if (className) parts.push(className);

  return (
    <span
      class={parts.join(" ")}
      style={style}
      data-polly-ui
      data-polly-skeleton={variant}
      aria-hidden="true"
    />
  );
}
