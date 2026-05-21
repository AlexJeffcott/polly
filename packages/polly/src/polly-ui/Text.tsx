/**
 * Text — typographic primitive for secondary and sized copy.
 *
 * Renders subtitles, captions, field labels, and empty-state copy
 * without the consumer reaching for a `style` attribute or a hand-rolled
 * `.muted` class. `tone` and `size` map to the semantic `--polly-text-*`
 * token family; `as` keeps the element polymorphic so the same
 * primitive backs a <span>, <p>, <label>, or <figcaption>. A no-prop
 * <Text> is an ordinary <span> at body size and default colour.
 */

import { type ComponentChildren, createElement, type JSX } from "preact";
import classes from "./Text.module.css";

export type TextTone = "default" | "muted";
export type TextSize = "xs" | "sm" | "md" | "lg" | "xl";
export type TextWeight = "normal" | "medium" | "bold";

export type TextProps = {
  children: ComponentChildren;

  /** Polymorphic element (span, p, label, figcaption, …). Defaults to 'span'. */
  as?: keyof JSX.IntrinsicElements;

  /** Colour role. 'muted' renders de-emphasised secondary text. Default: 'default'. */
  tone?: TextTone;

  /** Token-backed font size. Default: inherit from context. */
  size?: TextSize;

  /** Token-backed font weight. Default: inherit from context. */
  weight?: TextWeight;

  className?: string;
  id?: string;
  /** Forwarded so <Text as="label"> can point at a control. */
  htmlFor?: string;
  "aria-hidden"?: boolean;
};

export function Text(props: TextProps): JSX.Element {
  const { children, as = "span", tone = "default", size, weight, className, id } = props;

  const parts = [classes["text"]];
  if (tone === "muted") parts.push(classes["muted"]);
  if (size) parts.push(classes[size]);
  if (weight) parts.push(classes[weight]);
  if (className) parts.push(className);

  return createElement(
    as,
    {
      id,
      class: parts.filter(Boolean).join(" "),
      for: props.htmlFor,
      "data-polly-ui": true,
      "data-polly-text": tone,
      "aria-hidden": props["aria-hidden"],
    },
    children
  );
}
