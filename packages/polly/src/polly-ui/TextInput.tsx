/**
 * TextInput — passive, signal-friendly native input wrapper.
 *
 * Designed to live inside <ActionForm>. Pass a plain string for
 * uncontrolled mode (FormData-on-submit picks up the value) or a
 * Signal<string> for controlled mode. Either way, a11y attributes are
 * wired by the shared input-base, the stable `[data-polly-input]` hook
 * is applied for styling, and `invalid` flips `aria-invalid` and
 * `data-state="invalid"` for consumer selectors.
 *
 * `inputType` sets the native single-line input type — "text" (default),
 * "email", "number", "date", and friends — so the browser supplies the
 * right keyboard and validation. `min`/`max`/`step` apply to the
 * single-line variant (e.g. numeric or date bounds) and keep filter
 * fields from being unvalidated free text.
 *
 * `error`, when supplied, renders a message beneath the field, wraps the
 * control in a labelled group, and auto-wires `aria-describedby` plus the
 * invalid state — no manual id juggling. Without `error` the primitive
 * stays a bare native element, exactly as before, so consumers that own
 * their own surrounding structure are unaffected.
 */

import type { Signal } from "@preact/signals";
import type { JSX } from "preact";
import { useId } from "preact/hooks";
import { buildInputA11y } from "./internal/input-base.ts";
import classes from "./TextInput.module.css";

type Variant = "single" | "multi";

/** Native single-line input types polly's filter/form fields use. */
export type TextInputType =
  | "text"
  | "email"
  | "url"
  | "tel"
  | "search"
  | "password"
  | "number"
  | "date"
  | "datetime-local"
  | "time"
  | "month"
  | "week";

export type TextInputProps = {
  name: string;
  /** Signal<string> for controlled, string for uncontrolled default. */
  value?: Signal<string> | string;
  variant?: Variant;
  /** Native input type for the single-line variant. Default: "text". */
  inputType?: TextInputType;
  /** Lower bound for the single-line variant (number/date types). */
  min?: number | string;
  /** Upper bound for the single-line variant (number/date types). */
  max?: number | string;
  /** Step granularity for the single-line variant (number/date types). */
  step?: number | string;
  placeholder?: string;
  /** Native hover tooltip — a hint beyond the placeholder/label. */
  title?: string;
  invalid?: boolean;
  /**
   * Validation message rendered beneath the field. When present the
   * primitive wraps the control, links the message via aria-describedby,
   * and marks the field invalid. Omit it to keep a bare native element.
   */
  error?: string;
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
  return typeof v === "object" && v !== null && "value" in v && "peek" in (v as unknown as object);
}

export function TextInput(props: TextInputProps): JSX.Element {
  const variant = props.variant ?? "single";
  // Always called so hook order is stable; only used when `error` is set.
  const errorId = useId();
  const hasError = props.error !== undefined && props.error !== "";

  const describedBy =
    [props.describedBy, hasError ? errorId : undefined].filter(Boolean).join(" ") || undefined;

  const a11y = buildInputA11y({
    name: props.name,
    id: props.id,
    required: props.required,
    // An error message implies the field is invalid.
    invalid: props.invalid || hasError,
    describedBy,
    placeholder: props.placeholder,
    disabled: props.disabled,
    readOnly: props.readOnly,
  });

  const controlled = isSignal(props.value);
  const stringValue = controlled ? (props.value as unknown as Signal<string>).value : undefined;
  const defaultValue = controlled
    ? undefined
    : ((props.value as unknown as string | undefined) ?? "");

  const className = props.className ? `${classes["input"]} ${props.className}` : classes["input"];

  const onInput = (e: JSX.TargetedEvent<HTMLInputElement | HTMLTextAreaElement>): void => {
    if (controlled) {
      (props.value as unknown as Signal<string>).value = e.currentTarget.value;
    }
  };

  const control =
    variant === "multi" ? (
      <textarea
        {...(a11y as unknown as JSX.HTMLAttributes<HTMLTextAreaElement>)}
        class={className}
        title={props.title}
        data-polly-input-variant="multi"
        rows={props.rows}
        // biome-ignore lint/a11y/noAutofocus: opt-in prop — caller requests autofocus explicitly (e.g. form opens to this field).
        autoFocus={props.autoFocus}
        value={stringValue}
        defaultValue={defaultValue}
        onInput={onInput}
      />
    ) : (
      <input
        {...(a11y as unknown as JSX.HTMLAttributes<HTMLInputElement>)}
        type={props.inputType ?? "text"}
        class={className}
        title={props.title}
        data-polly-input-variant="single"
        min={props.min}
        max={props.max}
        step={props.step}
        // biome-ignore lint/a11y/noAutofocus: opt-in prop — caller requests autofocus explicitly (e.g. form opens to this field).
        autoFocus={props.autoFocus}
        value={stringValue}
        defaultValue={defaultValue}
        onInput={onInput}
      />
    );

  if (!hasError) return control;

  return (
    <div class={classes["field"]} data-polly-ui data-polly-field>
      {control}
      <span id={errorId} role="alert" class={classes["error"]}>
        {props.error}
      </span>
    </div>
  );
}
