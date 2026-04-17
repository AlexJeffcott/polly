/**
 * Select — dropdown of options with single- or multi-select semantics.
 *
 * Composes Dropdown for the menu and a native checkbox in each option
 * row for multi-select. The `selected` state is a Signal<Set<T>>;
 * single-select replaces the set, multi-select toggles membership.
 * Multi-select mode also shows Select All / Clear action buttons at
 * the top of the menu.
 */

import { type Signal, useComputed, useSignal } from "@preact/signals";
import type { JSX } from "preact";
import { Dropdown } from "./Dropdown.tsx";
import { Layout } from "./Layout.tsx";
import classes from "./Select.module.css";

export type SelectOption<T = string> = { value: T; label: string };

export type SelectProps<T = string> = {
  options: SelectOption<T>[];
  selected: Signal<Set<T>>;
  label?: string;
  placeholder?: string;
  multiSelect?: boolean;
  disabled?: boolean;
  className?: string;
  id?: string;
};

function formatSelected<T>(options: SelectOption<T>[], selected: Set<T>): string {
  if (selected.size === 0) return "";
  const labels: string[] = [];
  for (const opt of options) {
    if (selected.has(opt.value)) labels.push(opt.label);
  }
  return labels.join(", ");
}

export function Select<T = string>(props: SelectProps<T>): JSX.Element {
  const {
    options,
    selected,
    label,
    placeholder = "Select\u2026",
    multiSelect = false,
    disabled = false,
    className,
    id,
  } = props;

  const isOpen = useSignal(false);

  const displayText = useComputed(() => {
    const text = formatSelected(options, selected.value);
    return text.length > 0 ? text : placeholder;
  });

  const isEmpty = useComputed(() => selected.value.size === 0);

  const handleOptionClick = (value: T): void => {
    if (multiSelect) {
      const next = new Set(selected.value);
      if (next.has(value)) next.delete(value);
      else next.add(value);
      selected.value = next;
    } else {
      selected.value = new Set([value]);
      isOpen.value = false;
    }
  };

  const handleSelectAll = (): void => {
    selected.value = new Set(options.map((o) => o.value));
  };

  const handleClear = (): void => {
    selected.value = new Set();
  };

  const triggerClass = isEmpty.value
    ? `${classes["trigger"]} ${classes["placeholder"]}`
    : classes["trigger"];
  const triggerButton = (
    <button type="button" class={triggerClass} disabled={disabled}>
      {displayText.value}
    </button>
  );

  const parts = [classes["select"] ?? ""];
  if (className) parts.push(className);

  return (
    <div id={id} class={parts.filter(Boolean).join(" ")} data-polly-ui data-polly-select>
      {label !== undefined && <span class={classes["label"]}>{label}</span>}
      <Dropdown isOpen={isOpen} trigger={triggerButton} multiSelect={multiSelect}>
        {multiSelect && (
          <div class={classes["actions"]}>
            <Layout columns="1fr 1fr" gap="var(--polly-space-xs)">
              <button type="button" class={classes["actionBtn"]} onClick={handleSelectAll}>
                Select All
              </button>
              <button type="button" class={classes["actionBtn"]} onClick={handleClear}>
                Clear
              </button>
            </Layout>
          </div>
        )}
        {options.map((opt) => {
          const isSelected = selected.value.has(opt.value);
          const optClass = isSelected
            ? `${classes["option"]} ${classes["optionSelected"]}`
            : classes["option"];
          return (
            <button
              key={String(opt.value)}
              type="button"
              class={optClass}
              onClick={() => handleOptionClick(opt.value)}
            >
              {multiSelect && (
                <input
                  type="checkbox"
                  class={classes["optionCheck"]}
                  checked={isSelected}
                  tabIndex={-1}
                  readOnly={true}
                />
              )}
              <span>{opt.label}</span>
            </button>
          );
        })}
      </Dropdown>
    </div>
  );
}
