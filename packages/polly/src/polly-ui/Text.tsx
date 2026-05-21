/**
 * Text — typographic primitive for secondary, sized, and status copy.
 *
 * Renders subtitles, captions, field labels, empty-state copy, and
 * error/warning messages without the consumer reaching for a `style`
 * attribute or a hand-rolled class. `tone` maps to the semantic
 * `--polly-text-*` and `--polly-status-*` token families; `size`,
 * `weight`, `italic`, and `leading` cover the remaining typographic
 * axes. `as` keeps the element polymorphic so the same primitive backs a
 * <span>, <p>, <label>, or <figcaption>. A no-prop <Text> is an ordinary
 * <span> at body size and default colour.
 *
 * polly#125: arbitrary `data-*` / `aria-*` attributes are forwarded to
 * the rendered element, so a Text that also needs a test hook or an
 * a11y attribute stays a single element.
 */

import { type ComponentChildren, createElement, type JSX } from "preact";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";
import classes from "./Text.module.css";

export type TextTone = "default" | "muted" | "danger" | "warning" | "success";
export type TextSize = "xs" | "sm" | "md" | "lg" | "xl";
export type TextWeight = "normal" | "medium" | "bold";
export type TextLeading = "tight" | "base" | "loose";

export type TextProps = PassthroughAttrs & {
  children: ComponentChildren;

  /** Polymorphic element (span, p, label, figcaption, …). Defaults to 'span'. */
  as?: keyof JSX.IntrinsicElements;

  /** Colour role. 'muted' de-emphasises; 'danger'/'warning'/'success'
   * render status copy from the `--polly-status-*` tokens. Default: 'default'. */
  tone?: TextTone;

  /** Token-backed font size. Default: inherit from context. */
  size?: TextSize;

  /** Token-backed font weight. Default: inherit from context. */
  weight?: TextWeight;

  /** Italic emphasis — for hints and asides — without an inline style. */
  italic?: boolean;

  /** Token-backed line height. 'loose' suits multi-line body copy. */
  leading?: TextLeading;

  className?: string;
  id?: string;
  /** Forwarded so <Text as="label"> can point at a control. */
  htmlFor?: string;
};

export function Text(props: TextProps): JSX.Element {
  const {
    children,
    as = "span",
    tone = "default",
    size,
    weight,
    italic,
    leading,
    className,
    id,
  } = props;

  const parts = [classes["text"]];
  if (tone !== "default") parts.push(classes[tone]);
  if (size) parts.push(classes[size]);
  if (weight) parts.push(classes[weight]);
  if (italic) parts.push(classes["italic"]);
  if (leading) parts.push(classes[leading]);
  if (className) parts.push(className);

  return createElement(
    as,
    {
      // Consumer data-*/aria-* first; the primitive's own attributes
      // below win on any collision.
      ...collectPassthrough(props),
      id,
      class: parts.filter(Boolean).join(" "),
      for: props.htmlFor,
      "data-polly-ui": true,
      "data-polly-text": tone,
    },
    children
  );
}
