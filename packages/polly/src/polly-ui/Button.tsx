/**
 * Button — interactive control with tier, semantic colour, and size.
 *
 * Renders as a <button> by default; switches to an <a> when given an
 * `href`. Tier sets visual importance (primary/secondary/tertiary),
 * color overlays semantic meaning (info/success/warning/danger),
 * size picks the padding + font scale (small/normal/large). Icon +
 * label are arranged with a nested inline <Layout>.
 *
 * A text `label` is the accessible name. An icon-only button (icon, no
 * label) has none, so the type REQUIRES `aria-label` there — an unnamed
 * icon button won't compile. No build-time lint needed; the call site
 * itself is the gate.
 *
 * Action wiring is declared via data-* attributes consumed by the
 * global event delegator in @fairfox/polly/actions — Button does not
 * accept an onClick prop.
 *
 * Every button surfaces a native hover tooltip: an explicit `title`
 * wins, else the visible text label, else the `aria-label` (so an
 * icon-only button still gets one). Pass `title=""` to suppress it.
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
  /** Cap the button width at `--polly-control-max-width` and ellipsis-
   * truncate the label. Use for user-supplied or otherwise unbounded
   * labels so a long string doesn't blow out the row. */
  bounded?: boolean;
  className?: string;
  title?: string;
  "data-action"?: string;
  /** Additional action-payload attributes the event delegator parses
   * into `ctx.data`. `data-action-tid="t-17"` becomes `{ tid: "t-17" }`,
   * `data-action-item-id="…"` becomes `{ itemId: "…" }`, and so on.
   * Typed as an index signature so every `data-action-*` key the
   * consumer cares about type-checks without a Button-side enumeration. */
  [actionDataAttr: `data-action-${string}`]: string | undefined;
};

/**
 * Content/accessibility dimension. A visible text `label` is the
 * accessible name, so it makes `aria-label` optional. An icon-only
 * button has no text to name it, so `aria-label` is REQUIRED — you
 * cannot construct an unnamed icon button. (Button's hover title then
 * falls back to that aria-label, so the same prop gives both the
 * accessible name and the tooltip.)
 */
type LabelledContent = {
  label: ComponentChildren;
  icon?: VNode;
  "aria-label"?: string;
};
type IconOnlyContent = {
  icon: VNode;
  label?: never;
  "aria-label": string;
};
type ButtonContent = LabelledContent | IconOnlyContent;

type ButtonElement = {
  href?: never;
  target?: never;
  rel?: never;
  download?: never;
  type?: "button" | "submit" | "reset";
};

type LinkElement = {
  href: string;
  target?: string;
  rel?: string;
  /** Forwarded to the rendered <a> so a Button-as-link can offer a file
   * download. An empty string uses the resource's own filename. */
  download?: string;
  type?: never;
};

export type ButtonProps = BaseButtonProps & ButtonContent & (ButtonElement | LinkElement);

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
    bounded = false,
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
  if (bounded) parts.push(classes["btnBounded"] ?? "");
  if (className) parts.push(className);
  const buttonClass = parts.filter(Boolean).join(" ");

  const content = icon ? (
    <Layout inline columns="auto auto" gap="0.5em" alignItems="center">
      {icon}
      {label !== undefined && <span>{label}</span>}
    </Layout>
  ) : (
    label
  );

  const dataAction = props["data-action"];
  const ariaLabel = props["aria-label"];
  // Every button surfaces a hover tooltip: an explicit title wins, else the
  // visible text label, else the accessible name — so an icon-only button
  // (which carries an aria-label) still gets one. Pass title="" to opt out.
  const resolvedTitle =
    title ??
    (typeof label === "string" && label.length > 0
      ? label
      : typeof ariaLabel === "string"
        ? ariaLabel
        : undefined);
  // Collect every `data-action-*` extra the consumer passed so the
  // event delegator can read them off the rendered element. Without
  // this, anything beyond `data-action` is silently dropped and
  // handlers fire with an empty `ctx.data`.
  const actionDataAttrs: Record<string, string> = {};
  for (const key of Object.keys(props)) {
    if (key.startsWith("data-action-")) {
      const value = (props as unknown as Record<string, unknown>)[key];
      if (typeof value === "string") {
        actionDataAttrs[key] = value;
      }
    }
  }

  if ("href" in props && props.href) {
    return (
      <a
        id={id}
        class={buttonClass}
        title={resolvedTitle}
        href={disabled ? undefined : props.href}
        target={"target" in props ? props.target : undefined}
        rel={"rel" in props ? props.rel : undefined}
        download={"download" in props ? props.download : undefined}
        aria-disabled={disabled}
        aria-label={ariaLabel}
        data-polly-ui
        data-polly-button={tier}
        data-action={dataAction}
        {...actionDataAttrs}
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
      title={resolvedTitle}
      type={resolvedType}
      disabled={disabled}
      aria-label={ariaLabel}
      data-polly-ui
      data-polly-button={tier}
      data-action={dataAction}
      {...actionDataAttrs}
    >
      {content}
    </button>
  );
}
