/**
 * ActionSelect — single-select dropdown that commits via the action system.
 *
 * The action-dispatching sibling of <Select>. Where <Select> binds a
 * `Signal<Set<T>>` and is built for in-memory filter UIs, ActionSelect
 * takes the current `value` as a plain string and fires `action` with
 * `data-action-value` set to the chosen option — so editing a
 * server-backed field commits through the same event delegation as
 * <ActionInput> and <ActionForm>, with no synthetic signal or bridging
 * `effect` required.
 *
 * Composes <Dropdown> for the menu. The trigger styling is applied
 * directly to Dropdown's own <button> via `triggerClassName`, so the
 * visible box and the interactive element are one and the same node —
 * no styled <span> nested inside an unstyled <button>. A disabled
 * ActionSelect renders as static text without a caret.
 */

import { useSignal } from "@preact/signals";
import type { JSX } from "preact";
import { Dropdown } from "./Dropdown.tsx";
import { dispatchAction } from "./internal/dispatch-action.ts";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";
import classes from "./Select.module.css";
import type { SelectOption } from "./Select.tsx";

export type ActionSelectProps = PassthroughAttrs & {
  /** Current value — matched against `options` to render the trigger label. */
  value: string;
  /** Selectable options. */
  options: SelectOption<string>[];
  /** Action name to dispatch on selection. Receives data-action-value=<option value>. */
  action: string;
  /** Extra data-action-* attributes to include on commit (e.g. entity id). */
  actionData?: Record<string, string>;
  /** Visible field label rendered above the trigger. */
  label?: string;
  /** Trigger text shown when `value` matches no option. Default: "Select…". */
  placeholder?: string;
  disabled?: boolean;
  /** Apply a comfortable minimum width to the trigger. Default: sizes to content. */
  wide?: boolean;
  className?: string;
  id?: string;
};

function labelFor(options: SelectOption<string>[], value: string): string | undefined {
  for (const opt of options) {
    if (opt.value === value) return opt.label;
  }
  return undefined;
}

export function ActionSelect(props: ActionSelectProps): JSX.Element {
  const {
    value,
    options,
    action,
    actionData,
    label,
    placeholder = "Select…",
    disabled = false,
    wide = false,
    className,
    id,
  } = props;

  const isOpen = useSignal(false);

  const current = labelFor(options, value);
  const isEmpty = current === undefined;
  const displayText = current ?? placeholder;

  const commit = (next: string): void => {
    isOpen.value = false;
    if (next === value) return;
    dispatchAction(action, { ...(actionData ?? {}), value: next });
  };

  const triggerParts = [classes["trigger"] ?? ""];
  if (isEmpty) triggerParts.push(classes["placeholder"] ?? "");
  if (wide) triggerParts.push(classes["triggerWide"] ?? "");
  const triggerClass = triggerParts.filter(Boolean).join(" ");

  const parts = [classes["select"] ?? ""];
  if (className) parts.push(className);

  return (
    <div
      {...collectPassthrough(props)}
      id={id}
      class={parts.filter(Boolean).join(" ")}
      data-polly-ui
      data-polly-action-select
      data-state={isEmpty ? "empty" : "filled"}
    >
      {label !== undefined && <span class={classes["label"]}>{label}</span>}
      {disabled ? (
        <span class={triggerClass} aria-disabled="true">
          <span class={classes["triggerLabel"]}>{displayText}</span>
        </span>
      ) : (
        <Dropdown
          isOpen={isOpen}
          triggerClassName={triggerClass}
          trigger={
            <>
              <span class={classes["triggerLabel"]}>{displayText}</span>
              <span class={classes["caret"]} aria-hidden="true" />
            </>
          }
        >
          {options.map((opt) => {
            const isSelected = opt.value === value;
            const optClass = isSelected
              ? `${classes["option"]} ${classes["optionSelected"]}`
              : classes["option"];
            return (
              <button
                key={opt.value}
                type="button"
                role="option"
                class={optClass}
                aria-selected={isSelected ? "true" : "false"}
                onClick={() => commit(opt.value)}
              >
                <span>{opt.label}</span>
              </button>
            );
          })}
        </Dropdown>
      )}
    </div>
  );
}
