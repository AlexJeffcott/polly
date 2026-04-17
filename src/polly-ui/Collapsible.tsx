/**
 * Collapsible — native <details>/<summary> wrapper.
 *
 * Uses the browser's built-in disclosure semantics so keyboard and
 * screen-reader behaviour come free. A ::before arrow rotates on open.
 * Colors, spacing, and motion come from tokens; `prefers-reduced-motion`
 * zeroes the rotation via the motion token.
 */

import type { ComponentChildren, JSX } from "preact";
import classes from "./Collapsible.module.css";

export type CollapsibleProps = {
  summary: string;
  children: ComponentChildren;
  defaultOpen?: boolean;
  className?: string;
  id?: string;
};

export function Collapsible(props: CollapsibleProps): JSX.Element {
  const { summary, children, defaultOpen = false, className, id } = props;
  const parts = [classes["collapsible"]];
  if (className) parts.push(className);
  return (
    <details
      id={id}
      class={parts.join(" ")}
      open={defaultOpen}
      data-polly-ui
      data-polly-collapsible
    >
      <summary class={classes["summary"]}>{summary}</summary>
      <div class={classes["content"]}>{children}</div>
    </details>
  );
}
