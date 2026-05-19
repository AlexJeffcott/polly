/**
 * Shared input a11y wiring.
 *
 * Returns a common set of attributes that TextInput, ActionInput, and
 * any consumer-built input can splat onto its native element. Keeps
 * aria-* and data-polly-* names consistent across the family.
 */

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

export function buildInputA11y(props: InputA11yProps) {
  const attrs: Record<string, unknown> = {
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
