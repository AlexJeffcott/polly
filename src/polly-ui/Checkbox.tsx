/**
 * Checkbox — native checkbox wrapped in a label.
 *
 * Pass a plain boolean for controlled use (caller listens elsewhere),
 * or a Signal<boolean> to have the primitive bind its own change
 * listener and mutate the signal directly. The label wraps the input
 * so clicks anywhere in the target area toggle it.
 */

import type { Signal } from "@preact/signals";
import type { JSX } from "preact";
import classes from "./Checkbox.module.css";

export type CheckboxProps = {
  checked?: boolean | Signal<boolean>;
  defaultChecked?: boolean;
  name?: string;
  disabled?: boolean;
  label?: string;
  className?: string;
  id?: string;
};

function isSignal(value: unknown): value is Signal<boolean> {
  return typeof value === "object" && value !== null && "value" in value && "peek" in value;
}

export function Checkbox(props: CheckboxProps): JSX.Element {
  const { checked, defaultChecked, name, disabled = false, label, className, id } = props;

  const handleChange = (e: JSX.TargetedEvent<HTMLInputElement>): void => {
    if (isSignal(checked)) {
      checked.value = e.currentTarget.checked;
    }
  };

  const checkedValue = isSignal(checked) ? checked.value : checked;

  const parts = [classes["checkbox"]];
  if (disabled) parts.push(classes["disabled"] ?? "");
  if (className) parts.push(className);

  return (
    <label class={parts.filter(Boolean).join(" ")} data-polly-ui data-polly-checkbox>
      <input
        id={id}
        type="checkbox"
        class={classes["input"]}
        checked={checkedValue}
        defaultChecked={defaultChecked}
        name={name}
        disabled={disabled}
        onChange={handleChange}
      />
      {label !== undefined && <span class={classes["label"]}>{label}</span>}
    </label>
  );
}
