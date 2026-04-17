/**
 * Toggle — switch-role checkbox.
 *
 * A visually-hidden <input role="switch"> paired with a styled track
 * and thumb inside a <label>. Passive: the caller drives `checked` and
 * handles state changes via the action registry (wrap the Toggle in a
 * <label data-action="..."> or bind a parent form's submit). a11y
 * attributes come from the native input; the label wraps so clicks
 * anywhere in the control toggle the input.
 */

import type { JSX } from "preact";
import classes from "./Toggle.module.css";

export type ToggleProps = {
  checked?: boolean;
  disabled?: boolean;
  label?: string;
  name?: string;
  className?: string;
  id?: string;
};

export function Toggle(props: ToggleProps): JSX.Element {
  const { checked = false, disabled = false, label, name, className, id } = props;
  const parts = [classes["toggle"]];
  if (disabled) parts.push(classes["disabled"]);
  if (className) parts.push(className);
  return (
    <label class={parts.join(" ")} data-polly-ui data-polly-toggle>
      <input
        id={id}
        type="checkbox"
        role="switch"
        name={name}
        aria-checked={checked}
        class={classes["input"]}
        checked={checked}
        disabled={disabled}
      />
      <span class={checked ? `${classes["track"]} ${classes["trackChecked"]}` : classes["track"]}>
        <span
          class={checked ? `${classes["thumb"]} ${classes["thumbChecked"]}` : classes["thumb"]}
        />
      </span>
      {label !== undefined && <span class={classes["label"]}>{label}</span>}
    </label>
  );
}
