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
  /** Disclosure header. A string for the common case, or any node —
   * e.g. a muted, small <Text> — when the header needs styling. */
  summary: ComponentChildren;
  children: ComponentChildren;
  defaultOpen?: boolean;
  className?: string;
  id?: string;
};

/** Input types whose Space/Enter is an activation, not text entry — these
 * keep their own keyboard behaviour and must not be guarded. */
const NON_TEXT_INPUT_TYPES = new Set([
  "checkbox",
  "radio",
  "button",
  "submit",
  "reset",
  "file",
  "image",
  "range",
  "color",
]);

/** Is the event target a field where Space/Enter inserts/edits text? */
function isTextEntryTarget(target: EventTarget | null): boolean {
  if (!(target instanceof HTMLElement)) return false;
  if (target instanceof HTMLTextAreaElement) return true;
  if (target.isContentEditable) return true;
  if (target instanceof HTMLInputElement) {
    return !NON_TEXT_INPUT_TYPES.has(target.type);
  }
  return false;
}

/**
 * Chromium toggles a <details> on the Space/Enter *keyup* of its <summary>,
 * even when focus sits in a nested text field — so every space typed in an
 * editable header would collapse the disclosure. stopPropagation can't stop
 * it (the toggle is the summary's own activation behaviour, not a bubbling
 * listener) and preventDefault on *keydown* would swallow the character. The
 * character is already inserted by the time keyup fires, so cancelling the
 * keyup default for text-entry fields kills the toggle while leaving typing
 * untouched. Buttons/checkbox/radio fall through and keep their own
 * activation; the summary itself (no nested field) keeps normal keyboard
 * disclosure.
 */
function handleSummaryKeyUp(event: JSX.TargetedKeyboardEvent<HTMLElement>): void {
  if (event.key !== " " && event.key !== "Enter") return;
  if (!isTextEntryTarget(event.target)) return;
  event.preventDefault();
}

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
      {/* biome-ignore lint/a11y/noStaticElementInteractions: <summary> is a native interactive disclosure control; this keyup guard cancels its toggle when a nested editable field is the target. */}
      <summary class={classes["summary"]} onKeyUp={handleSummaryKeyUp}>
        {summary}
      </summary>
      <div class={classes["content"]}>{children}</div>
    </details>
  );
}
