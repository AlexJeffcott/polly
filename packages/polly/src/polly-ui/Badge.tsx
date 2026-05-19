/**
 * Badge — small inline status chip.
 *
 * Renders as a passive <span> with tinted background and on-tint text
 * from the `--polly-status-*` token family. The default variant uses
 * surface-sunken + muted text for a neutral pill. Consumers style
 * placement via className; the primitive owns size, shape, and colour.
 */

import type { ComponentChildren, JSX } from "preact";
import classes from "./Badge.module.css";

export type BadgeVariant = "default" | "info" | "success" | "warning" | "danger";

export type BadgeProps = {
  children: ComponentChildren;
  variant?: BadgeVariant;
  className?: string;
  id?: string;
};

function variantClass(variant: BadgeVariant): string | undefined {
  if (variant === "info") return classes["info"];
  if (variant === "success") return classes["success"];
  if (variant === "warning") return classes["warning"];
  if (variant === "danger") return classes["danger"];
  return undefined;
}

export function Badge(props: BadgeProps): JSX.Element {
  const { children, variant = "default", className, id } = props;
  const parts = [classes["badge"]];
  const v = variantClass(variant);
  if (v) parts.push(v);
  if (className) parts.push(className);
  return (
    <span id={id} class={parts.join(" ")} data-polly-ui data-polly-badge={variant}>
      {children}
    </span>
  );
}
