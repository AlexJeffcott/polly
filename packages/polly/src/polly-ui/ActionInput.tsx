/**
 * ActionInput — dual-mode view/edit input with action dispatch on commit.
 *
 * View mode renders the current value as text (optionally through a
 * caller-supplied `renderView` for markdown, rich formatting, etc.).
 * Click, Enter, or Space enters edit mode. Edit mode is a native input
 * or textarea; commit fires the configured action with `data-action-value`
 * and `data-action-field` set from FormData-shape semantics, so the
 * existing event delegation handles it with no extra wiring.
 *
 * `saveOn` picks the commit trigger:
 *   "blur"       commit when the field loses focus
 *   "enter"      commit on Enter (single-line) or Cmd/Ctrl+Enter (multi-line)
 *   "cmd-enter"  commit only on Cmd/Ctrl+Enter
 *   "explicit"   never auto-commit — caller wires a save button with data-action
 *
 * Layout-shift-free: view and edit modes share padding, border width,
 * font, and line-height so the toggle causes no reflow.
 */

import type { JSX } from "preact";
import { useCallback, useEffect, useRef, useState } from "preact/hooks";
import classes from "./ActionInput.module.css";

export type ActionInputSaveOn = "blur" | "enter" | "cmd-enter" | "explicit";
export type ActionInputVariant = "single" | "multi";

export type ActionInputProps = {
  /** Current value to render in view mode and seed the edit buffer. */
  value: string;
  /** Action name to dispatch on commit. Receives data-action-value=<new value>. */
  action: string;
  /** Commit trigger. Default: "blur". */
  saveOn?: ActionInputSaveOn;
  variant?: ActionInputVariant;
  placeholder?: string;
  disabled?: boolean;
  /** Extra data-action-* attributes to include at commit (e.g. entity id). */
  actionData?: Record<string, string>;
  /** Custom view renderer — receives value, returns VNode. */
  renderView?: (value: string) => JSX.Element | string;
  /** Label announced by screen readers for the edit affordance. */
  ariaLabel?: string;
  className?: string;
};

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: two render branches times two variants times four saveOn triggers; branching is inherent to the primitive.
export function ActionInput(props: ActionInputProps): JSX.Element {
  const variant = props.variant ?? "single";
  const saveOn = props.saveOn ?? "blur";
  const [mode, setMode] = useState<"view" | "edit">("view");
  const [draft, setDraft] = useState(props.value);
  const inputRef = useRef<HTMLInputElement | HTMLTextAreaElement | null>(null);

  useEffect(() => {
    if (mode === "view") setDraft(props.value);
  }, [props.value, mode]);

  useEffect(() => {
    if (mode === "edit" && inputRef.current) {
      inputRef.current.focus();
      inputRef.current.select?.();
    }
  }, [mode]);

  const enterEdit = useCallback(() => {
    if (props.disabled) return;
    setDraft(props.value);
    setMode("edit");
  }, [props.disabled, props.value]);

  const commit = useCallback(
    (next: string) => {
      if (next === props.value) {
        setMode("view");
        return;
      }
      const dataAttrs: Record<string, string> = {
        ...(props.actionData ?? {}),
        value: next,
      };
      const hidden = document.createElement("button");
      hidden.setAttribute("data-action", props.action);
      for (const [key, value] of Object.entries(dataAttrs)) {
        const dashKey = key.replace(/[A-Z]/g, (m) => `-${m.toLowerCase()}`);
        hidden.setAttribute(`data-action-${dashKey}`, value);
      }
      hidden.style.position = "fixed";
      hidden.style.opacity = "0";
      hidden.style.pointerEvents = "none";
      hidden.tabIndex = -1;
      document.body.appendChild(hidden);
      try {
        hidden.click();
      } finally {
        hidden.remove();
      }
      setMode("view");
    },
    [props.action, props.actionData, props.value]
  );

  const cancel = useCallback(() => {
    setDraft(props.value);
    setMode("view");
  }, [props.value]);

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: keyboard handler encodes the saveOn × variant matrix.
  const onKeyDown = (event: JSX.TargetedKeyboardEvent<HTMLInputElement | HTMLTextAreaElement>) => {
    if (event.key === "Escape") {
      event.preventDefault();
      cancel();
      return;
    }
    if (event.key === "Enter") {
      const cmd = event.metaKey || event.ctrlKey;
      if (saveOn === "enter" && variant === "single") {
        event.preventDefault();
        commit(draft);
      } else if ((saveOn === "enter" && variant === "multi" && cmd) || saveOn === "cmd-enter") {
        if (cmd) {
          event.preventDefault();
          commit(draft);
        }
      }
    }
  };

  const className = props.className ? `${classes["root"]} ${props.className}` : classes["root"];

  if (mode === "view") {
    const rendered = props.renderView ? props.renderView(props.value) : props.value;
    const isEmpty = props.value.length === 0;
    return (
      // biome-ignore lint/a11y/useSemanticElements: <button> would swallow text selection and add default styling; div with role=button is the inline-edit idiom.
      <div
        class={`${className} ${classes["view"]}`}
        data-polly-ui
        data-polly-action-input
        data-polly-interactive
        data-state={isEmpty ? "empty" : "filled"}
        data-variant={variant}
        tabIndex={props.disabled ? -1 : 0}
        role="button"
        aria-label={props.ariaLabel ?? "Edit"}
        aria-disabled={props.disabled ? "true" : undefined}
        onClick={enterEdit}
        onKeyDown={(e) => {
          if (e.key === "Enter" || e.key === " ") {
            e.preventDefault();
            enterEdit();
          }
        }}
      >
        {isEmpty && props.placeholder ? (
          <span class={classes["placeholder"]}>{props.placeholder}</span>
        ) : (
          rendered
        )}
      </div>
    );
  }

  const common = {
    class: `${classes["edit"]} ${classes["root"]}`,
    "data-polly-ui": true,
    "data-polly-action-input": true,
    "data-state": "editing",
    "data-variant": variant,
    placeholder: props.placeholder,
    value: draft,
    onInput: (e: JSX.TargetedEvent<HTMLInputElement | HTMLTextAreaElement>) =>
      setDraft(e.currentTarget.value),
    onBlur: () => {
      if (saveOn === "blur") commit(draft);
      else cancel();
    },
    onKeyDown,
    "aria-label": props.ariaLabel ?? "Edit",
    disabled: props.disabled,
  };

  if (variant === "multi") {
    return (
      <textarea
        ref={(el) => {
          inputRef.current = el;
        }}
        {...(common as unknown as JSX.HTMLAttributes<HTMLTextAreaElement>)}
      />
    );
  }
  return (
    <input
      ref={(el) => {
        inputRef.current = el;
      }}
      type="text"
      {...(common as unknown as JSX.HTMLAttributes<HTMLInputElement>)}
    />
  );
}
