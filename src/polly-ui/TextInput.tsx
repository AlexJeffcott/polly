/**
 * TextInput — passive, signal-friendly native input wrapper.
 *
 * Designed to live inside <ActionForm>. Pass a plain string for
 * uncontrolled mode (FormData-on-submit picks up the value) or a
 * Signal<string> for controlled mode. Either way, a11y attributes are
 * wired by the shared input-base, the stable `[data-polly-input]` hook
 * is applied for styling, and `invalid` flips `aria-invalid` and
 * `data-state="invalid"` for consumer selectors.
 */

import type { Signal } from "@preact/signals";
import type { JSX } from "preact";
import { buildInputA11y } from "./internal/input-base.ts";
import classes from "./TextInput.module.css";

type Variant = "single" | "multi";

export type TextInputProps = {
  name: string;
  /** Signal<string> for controlled, string for uncontrolled default. */
  value?: Signal<string> | string;
  variant?: Variant;
  placeholder?: string;
  invalid?: boolean;
  required?: boolean;
  disabled?: boolean;
  readOnly?: boolean;
  id?: string;
  describedBy?: string;
  rows?: number;
  autoFocus?: boolean;
  className?: string;
};

function isSignal<T>(v: Signal<T> | T | undefined): v is Signal<T> {
  return typeof v === "object" && v !== null && "value" in v && "peek" in (v as object);
}

export function TextInput(props: TextInputProps): JSX.Element {
  const variant = props.variant ?? "single";
  const a11y = buildInputA11y({
    name: props.name,
    id: props.id,
    required: props.required,
    invalid: props.invalid,
    describedBy: props.describedBy,
    placeholder: props.placeholder,
    disabled: props.disabled,
    readOnly: props.readOnly,
  });

  const controlled = isSignal(props.value);
  const stringValue = controlled ? (props.value as Signal<string>).value : undefined;
  const defaultValue = controlled ? undefined : ((props.value as string | undefined) ?? "");

  const className = props.className ? `${classes["input"]} ${props.className}` : classes["input"];

  if (variant === "multi") {
    return (
      <textarea
        {...(a11y as unknown as JSX.HTMLAttributes<HTMLTextAreaElement>)}
        class={className}
        data-polly-input-variant="multi"
        rows={props.rows}
        // biome-ignore lint/a11y/noAutofocus: opt-in prop — caller requests autofocus explicitly (e.g. form opens to this field).
        autoFocus={props.autoFocus}
        value={stringValue}
        defaultValue={defaultValue}
        onInput={(e) => {
          if (controlled) {
            (props.value as Signal<string>).value = e.currentTarget.value;
          }
        }}
      />
    );
  }

  return (
    <input
      {...(a11y as unknown as JSX.HTMLAttributes<HTMLInputElement>)}
      type="text"
      class={className}
      data-polly-input-variant="single"
      // biome-ignore lint/a11y/noAutofocus: opt-in prop — caller requests autofocus explicitly (e.g. form opens to this field).
      autoFocus={props.autoFocus}
      value={stringValue}
      defaultValue={defaultValue}
      onInput={(e) => {
        if (controlled) {
          (props.value as Signal<string>).value = e.currentTarget.value;
        }
      }}
    />
  );
}
