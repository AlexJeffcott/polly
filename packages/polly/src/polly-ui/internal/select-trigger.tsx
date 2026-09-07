/**
 * SelectTrigger — the label/caret row inside a select trigger box.
 *
 * `.trigger` in Select.module.css styles the *box*: border, padding,
 * `min-block-size`, and `align-content: center` to centre one child in
 * it. It deliberately declares no flex or grid of its own — polly-ui
 * routes every layout decision through <Layout> — so the component
 * that applies `.trigger` must supply the row.
 *
 * polly#180: that rule was changed for one of its two consumers.
 * <Select> gained a <Layout>; <ActionSelect>, which applies the same
 * class through Dropdown's `triggerClassName`, kept rendering two bare
 * inline spans, so its caret wrapped onto a second line. Nothing tied
 * the stylesheet's contract to the components that had to satisfy it.
 * This module is that tie: one row, one definition, both consumers.
 */

import type { JSX } from "preact";
import { Layout } from "../Layout.tsx";
import classes from "../Select.module.css";

export type SelectTriggerProps = {
  /** Text in the trigger — the current selection, or the placeholder. */
  label: string;
  /**
   * Render the dropdown caret beside the label. Off for a disabled
   * <ActionSelect>, which is static text with no menu to open.
   */
  caret?: boolean;
  /**
   * Element the row renders as. `span` where the trigger box is itself
   * phrasing content — a disabled <ActionSelect> renders its box as a
   * <span>, which may not contain a <div>.
   */
  as?: "div" | "span";
};

export function SelectTrigger(props: SelectTriggerProps): JSX.Element {
  const { label, caret = true, as = "div" } = props;
  return (
    <Layout
      as={as}
      inline
      // Without a caret the second track would still contribute its gap,
      // padding the trigger by 8px it does not need.
      columns={caret ? "1fr auto" : "1fr"}
      {...(caret ? { gap: "var(--polly-space-sm)" } : {})}
      alignItems="center"
      maxInlineSize="100%"
    >
      {/* The 1fr track blockifies this span, which is what lets
          `text-overflow: ellipsis` apply to a long label. */}
      <span class={classes["triggerLabel"]} data-polly-select-label>
        {label}
      </span>
      {caret && <span class={classes["caret"]} aria-hidden="true" />}
    </Layout>
  );
}
