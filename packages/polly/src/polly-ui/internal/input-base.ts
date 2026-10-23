/**
 * Shared input a11y wiring.
 *
 * Returns a common set of attributes that TextInput, ActionInput, and
 * any consumer-built input can splat onto its native element. Keeps
 * aria-* and data-polly-* names consistent across the family.
 */

import type { InputAriaRoles } from "preact";
import type { TextInputType } from "../TextInput.tsx";

/**
 * One `{ type }` object per native input type. preact's input attributes
 * are a union discriminated by `type`, so `type={union}` does not
 * type-check; indexing this table yields a union of members that do.
 */
const INPUT_TYPE_ATTRS = {
  text: { type: "text" },
  email: { type: "email" },
  url: { type: "url" },
  tel: { type: "tel" },
  search: { type: "search" },
  password: { type: "password" },
  number: { type: "number" },
  date: { type: "date" },
  "datetime-local": { type: "datetime-local" },
  time: { type: "time" },
  month: { type: "month" },
  week: { type: "week" },
} as const satisfies { [K in TextInputType]: InputAriaRoles & { type: K } };

/** The `type` attribute for a native single-line input, splattable onto `<input>`. */
export function inputTypeAttrs<K extends TextInputType>(type: K): (typeof INPUT_TYPE_ATTRS)[K] {
  return INPUT_TYPE_ATTRS[type];
}

export type InputA11yProps = {
  name?: string;
  id?: string;
  required?: boolean;
  invalid?: boolean;
  describedBy?: string;
  placeholder?: string;
  disabled?: boolean;
  readOnly?: boolean;
};

/** The attributes `buildInputA11y` returns, ready to splat onto an input. */
export type InputA11yAttributes = {
  "data-polly-ui": true;
  "data-polly-input": true;
  "data-state"?: "invalid";
  "aria-invalid": "true" | undefined;
  "aria-required": "true" | undefined;
  "aria-describedby": string | undefined;
  name: string | undefined;
  id: string | undefined;
  placeholder: string | undefined;
  disabled: boolean | undefined;
  readOnly: boolean | undefined;
};

export function buildInputA11y(props: InputA11yProps): InputA11yAttributes {
  const attrs: InputA11yAttributes = {
    "data-polly-ui": true,
    "data-polly-input": true,
    "aria-invalid": props.invalid ? "true" : undefined,
    "aria-required": props.required ? "true" : undefined,
    "aria-describedby": props.describedBy,
    name: props.name,
    id: props.id,
    placeholder: props.placeholder,
    disabled: props.disabled,
    readOnly: props.readOnly,
  };
  if (props.invalid) attrs["data-state"] = "invalid";
  return attrs;
}
