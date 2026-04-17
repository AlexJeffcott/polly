/**
 * Button — interactive control with tier, semantic colour, and size.
 *
 * Renders as a <button> by default; switches to an <a> when given an
 * `href`. Tier sets visual importance (primary/secondary/tertiary),
 * color overlays semantic meaning (info/success/warning/danger),
 * size picks the padding + font scale (small/normal/large). Icon +
 * label are arranged with a nested inline <Layout>.
 *
 * Action wiring is declared via data-* attributes consumed by the
 * global event delegator in @fairfox/polly/actions — Button does not
 * accept an onClick prop.
 */

import type { ComponentChildren, JSX, VNode } from "preact";
import classes from "./Button.module.css";
import { Layout } from "./Layout.tsx";

export type ButtonTier = "primary" | "secondary" | "tertiary";
export type ButtonColor = "default" | "info" | "success" | "warning" | "danger";
export type ButtonSize = "small" | "normal" | "large";

type BaseButtonProps = {
  id?: string;
  tier?: ButtonTier;
  color?: ButtonColor;
  size?: ButtonSize;
  disabled?: boolean;
  fullWidth?: boolean;
  circle?: boolean;
  className?: string;
  title?: string;
  icon?: VNode;
  label: ComponentChildren;
  "data-action"?: string;
  "aria-label"?: string;
};

type ButtonAsButton = BaseButtonProps & {
  href?: never;
  target?: never;
  rel?: never;
  type?: "button" | "submit" | "reset";
};

type ButtonAsLink = BaseButtonProps & {
  href: string;
  target?: string;
  rel?: string;
  type?: never;
};

export type ButtonProps = ButtonAsButton | ButtonAsLink;

function tierClass(tier: ButtonTier): string | undefined {
  if (tier === "primary") return classes["tierPrimary"];
  if (tier === "tertiary") return classes["tierTertiary"];
  return classes["tierSecondary"];
}

function colorClass(color: ButtonColor): string | undefined {
  if (color === "info") return classes["colorInfo"];
  if (color === "success") return classes["colorSuccess"];
  if (color === "warning") return classes["colorWarning"];
  if (color === "danger") return classes["colorDanger"];
  return undefined;
}

function sizeClass(size: ButtonSize): string | undefined {
  if (size === "small") return classes["btnSmall"];
  if (size === "large") return classes["btnLarge"];
  return undefined;
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: flat prop-to-class composition plus one anchor/button branch; splitting would just hide the mapping.
export function Button(props: ButtonProps): JSX.Element {
  const {
    id,
    tier = "secondary",
    color = "default",
    size = "normal",
    disabled = false,
    fullWidth = false,
    circle = false,
    className,
    title,
    icon,
    label,
  } = props;

  const parts = [classes["btn"] ?? ""];
  const tc = tierClass(tier);
  if (tc) parts.push(tc);
  const cc = colorClass(color);
  if (cc) parts.push(cc);
  const sc = sizeClass(size);
  if (sc) parts.push(sc);
  if (circle) parts.push(classes["btnCircle"] ?? "");
  if (fullWidth) parts.push(classes["btnFullWidth"] ?? "");
  if (className) parts.push(className);
  const buttonClass = parts.filter(Boolean).join(" ");

  const content = icon ? (
    <Layout inline columns="auto auto" gap="0.5em" alignItems="center">
      {icon}
      <span>{label}</span>
    </Layout>
  ) : (
    label
  );

  const dataAction = props["data-action"];
  const ariaLabel = props["aria-label"];

  if ("href" in props && props.href) {
    return (
      <a
        id={id}
        class={buttonClass}
        title={title}
        href={disabled ? undefined : props.href}
        target={"target" in props ? props.target : undefined}
        rel={"rel" in props ? props.rel : undefined}
        aria-disabled={disabled}
        aria-label={ariaLabel}
        data-polly-ui
        data-polly-button={tier}
        data-action={dataAction}
      >
        {content}
      </a>
    );
  }

  const resolvedType: "button" | "submit" | "reset" =
    "type" in props && props.type ? props.type : "button";

  return (
    <button
      id={id}
      class={buttonClass}
      title={title}
      type={resolvedType}
      disabled={disabled}
      aria-label={ariaLabel}
      data-polly-ui
      data-polly-button={tier}
      data-action={dataAction}
    >
      {content}
    </button>
  );
}
