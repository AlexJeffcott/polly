/**
 * Cluster — wrapping row of variable-width items.
 *
 * The flex-wrap counterpart to <Layout>. Where Layout owns CSS grid
 * tracks, Cluster owns a row of items that differ in width and must
 * reflow as space runs out — filter chips, tag and badge lists, groups
 * of small buttons. Items keep even spacing on both axes via `gap`; the
 * row wraps automatically at narrow widths. Like Layout, props map to
 * CSS custom properties so consumers can override any of them in a
 * media query without touching specificity.
 *
 * This is the second (and final) layout primitive: a consumer never
 * writes `display: flex` or `display: grid` themselves — grid goes
 * through <Layout>, a wrapping cluster goes through <Cluster>.
 */

import { type ComponentChildren, createElement, type JSX } from "preact";
import classes from "./Cluster.module.css";

export type ClusterProps = {
  children: ComponentChildren;

  /** Polymorphic element (div, nav, ul, …). Defaults to 'div'. */
  as?: keyof JSX.IntrinsicElements;

  /** Space between items, both axes. Typically a `--polly-space-*` token. */
  gap?: string;
  padding?: string;

  /** Main-axis distribution — maps to justify-content. Default: start. */
  justify?: string;
  /** Cross-axis alignment within a wrapped row — maps to align-items. Default: center. */
  align?: string;

  /** Render as inline-flex so the cluster flows inline with surrounding text. */
  inline?: boolean;

  className?: string;
  id?: string;
  role?: JSX.AriaRole;
  "aria-label"?: string;
};

export function Cluster(props: ClusterProps): JSX.Element {
  const { children, as = "div", gap, padding, justify, align, inline, className, id, role } = props;

  const style: Record<string, string> = {};
  if (gap) style["--c-gap"] = gap;
  if (padding) style["--c-p"] = padding;
  if (justify) style["--c-jc"] = justify;
  if (align) style["--c-ai"] = align;

  const parts = [classes["cluster"]];
  if (inline) parts.push(classes["inline"]);
  if (className) parts.push(className);

  return createElement(
    as,
    {
      id,
      class: parts.filter(Boolean).join(" "),
      style,
      role,
      "aria-label": props["aria-label"],
      "data-polly-ui": true,
      "data-polly-cluster": true,
    },
    children
  );
}
