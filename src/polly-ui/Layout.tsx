/**
 * Layout — the one primitive that owns layouting concerns.
 *
 * Every other component in @fairfox/polly/ui (and every consumer app
 * that runs `polly quality css-layout`) routes flex/grid decisions
 * through this component. Props map to CSS custom properties so the
 * stylesheet can read them uniformly and so consumers can override
 * any of them in media queries without touching specificity.
 */

import {
  type ComponentChildren,
  createElement,
  type JSX,
} from "preact";
import classes from "./Layout.module.css";

export type LayoutProps = {
  children: ComponentChildren;

  /** Polymorphic element (div, section, header, nav, …). Defaults to 'div'. */
  as?: keyof JSX.IntrinsicElements;

  /** CSS grid structure. */
  rows?: string;
  columns?: string;
  autoFlow?: string;
  autoRows?: string;
  autoColumns?: string;

  /** display: contents — lets children participate in an ancestor grid. */
  contents?: boolean;
  /** Inherit parent grid tracks via CSS subgrid. */
  subgrid?: boolean;

  /** Spacing. */
  gap?: string;
  padding?: string;

  /** Sizing. */
  height?: string;
  minHeight?: string;

  /** Container alignment. */
  justifyItems?: string;
  alignItems?: string;
  justifyContent?: string;
  alignContent?: string;

  /** Self alignment (when this Layout is an item in a parent grid). */
  justifySelf?: string;
  alignSelf?: string;

  /** Collapse to a single column at ≤640px. */
  stackOnMobile?: boolean;

  className?: string;
  onClick?: JSX.MouseEventHandler<HTMLElement>;
  onKeyDown?: JSX.KeyboardEventHandler<HTMLElement>;

  role?: JSX.AriaRole;
  tabIndex?: number;
  id?: string;
  "aria-label"?: string;
  "aria-labelledby"?: string;
  "aria-describedby"?: string;
};

export function Layout(props: LayoutProps): JSX.Element {
  const {
    children,
    as = "div",
    rows,
    columns,
    contents,
    subgrid,
    gap,
    padding,
    height,
    minHeight,
    justifyItems,
    alignItems,
    justifyContent,
    alignContent,
    justifySelf,
    alignSelf,
    autoFlow,
    autoRows,
    autoColumns,
    stackOnMobile,
    className,
    onClick,
    onKeyDown,
    role,
    tabIndex,
    id,
  } = props;

  const style: Record<string, string> = {};

  if (contents) {
    style["display"] = "contents";
  } else if (subgrid) {
    style["--l-col"] = "1 / -1";
    style["--l-cols"] = "subgrid";
    if (padding) style["--l-p"] = padding;
    if (alignItems) style["--l-ai"] = alignItems;
    if (gap) style["--l-gap"] = gap;
  } else {
    if (padding) style["--l-p"] = padding;
    if (height) style["--l-h"] = height;
    if (minHeight) style["--l-mh"] = minHeight;
    if (rows) style["--l-rows"] = rows;
    if (columns) style["--l-cols"] = columns;
    if (gap) style["--l-gap"] = gap;
    if (justifyItems) style["--l-ji"] = justifyItems;
    if (alignItems) style["--l-ai"] = alignItems;
    if (justifyContent) style["--l-jc"] = justifyContent;
    if (alignContent) style["--l-ac"] = alignContent;
    if (autoFlow) style["--l-flow"] = autoFlow;
    if (autoRows) style["--l-arows"] = autoRows;
    if (autoColumns) style["--l-acols"] = autoColumns;
  }
  if (justifySelf) style["--l-js"] = justifySelf;
  if (alignSelf) style["--l-as"] = alignSelf;

  const baseClass = stackOnMobile
    ? `${classes["layout"]} ${classes["stackOnMobile"]}`
    : classes["layout"];
  const combined = contents
    ? className
    : className
      ? `${baseClass} ${className}`
      : baseClass;

  return createElement(
    as,
    {
      id,
      className: combined,
      style,
      onClick,
      onKeyDown,
      role,
      tabIndex,
      "aria-label": props["aria-label"],
      "aria-labelledby": props["aria-labelledby"],
      "aria-describedby": props["aria-describedby"],
      "data-polly-layout": true,
    },
    children,
  );
}
