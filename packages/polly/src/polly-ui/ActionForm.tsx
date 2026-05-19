/**
 * ActionForm — wraps a native <form> with the action pattern.
 *
 * Renders <form data-action="{form.name}:submit"> so the installed
 * event delegation catches the submit event and dispatches to the
 * form's auto-registered :submit handler. `aria-busy` mirrors the
 * `isSubmitting` signal so consumer styling can respond without extra
 * wiring. The form element also exposes `data-polly-action-form` for
 * stable selector hooks.
 */

import type { ComponentChildren, JSX } from "preact";
import type { FormStore } from "../actions/form.ts";
import classes from "./ActionForm.module.css";

export type ActionFormProps<TValues extends Record<string, string>, TStores> = {
  form: FormStore<TValues, TStores>;
  children: ComponentChildren;
  className?: string;
  id?: string;
  "aria-label"?: string;
  "aria-labelledby"?: string;
};

export function ActionForm<TValues extends Record<string, string>, TStores>(
  props: ActionFormProps<TValues, TStores>
): JSX.Element {
  const { form, children, className, id } = props;
  const combined = className ? `${classes["form"]} ${className}` : classes["form"];
  return (
    <form
      id={id}
      class={combined}
      data-polly-ui
      data-polly-action-form={form.name}
      data-action={`${form.name}:submit`}
      aria-busy={form.isSubmitting.value}
      aria-label={props["aria-label"]}
      aria-labelledby={props["aria-labelledby"]}
      noValidate
    >
      {children}
    </form>
  );
}
