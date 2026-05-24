/**
 * Output — read-only, multi-line diagnostic text.
 *
 * For program output a consumer must SHOW but not edit: a mesh-state
 * snapshot, a per-peer sync table, a recovery blob. <TextInput> and
 * <ActionInput> are single-line and editable; <Code> is for code
 * samples and never wraps. <Output> renders a monospace <pre> that
 * wraps long lines by default — a diagnostic dump should stay on
 * screen — with `scroll` to switch to a horizontal scrollbar instead.
 *
 * It carries the polly#125 passthrough surface, so a `data-action`
 * for a tap-to-select-all gesture rides straight onto the <pre>
 * (polly#135).
 */

import type { ComponentChildren, JSX } from "preact";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";
import classes from "./Output.module.css";

export type OutputProps = PassthroughAttrs & {
  children: ComponentChildren;
  /** Scroll long unbreakable lines horizontally instead of wrapping. */
  scroll?: boolean;
  /** Make the block focusable — pair with a `data-action` tap gesture. */
  tabIndex?: number;
  className?: string;
  id?: string;
};

export function Output(props: OutputProps): JSX.Element {
  const { children, scroll, tabIndex, className, id } = props;

  const parts = [classes["output"]];
  if (scroll) parts.push(classes["scroll"]);
  if (className) parts.push(className);

  return (
    <pre
      {...collectPassthrough(props)}
      id={id}
      class={parts.filter(Boolean).join(" ")}
      tabIndex={tabIndex}
      data-polly-ui
      data-polly-output
    >
      {children}
    </pre>
  );
}
