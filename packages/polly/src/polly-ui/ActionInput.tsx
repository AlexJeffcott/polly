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
 *   "input"      commit on every keystroke — for filter-as-you-type fields;
 *                the field stays in edit mode rather than toggling to view
 *
 * `inputType` sets the native input type for the single-line variant —
 * "text" (default), "date", "time", "number", and friends — so a date
 * or numeric field commits through the action system like any other.
 *
 * Layout-shift-free: view and edit modes share padding, border width,
 * font, and line-height so the toggle causes no reflow.
 */

import type { JSX } from "preact";
import { useCallback, useEffect, useRef, useState } from "preact/hooks";
import classes from "./ActionInput.module.css";
import { dispatchAction } from "./internal/dispatch-action.ts";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";

export type ActionInputSaveOn = "blur" | "enter" | "cmd-enter" | "explicit" | "input";
export type ActionInputVariant = "single" | "multi";
export type ActionInputType =
  | "text"
  | "date"
  | "datetime-local"
  | "time"
  | "month"
  | "week"
  | "number"
  | "email"
  | "url"
  | "tel";

export type ActionInputProps = PassthroughAttrs & {
  /** Current value to render in view mode and seed the edit buffer. */
  value: string;
  /** Action name to dispatch on commit. Receives data-action-value=<new value>. */
  action: string;
  /** Commit trigger. Default: "blur". */
  saveOn?: ActionInputSaveOn;
  variant?: ActionInputVariant;
  /** Native input type for the single-line variant. Default: "text". */
  inputType?: ActionInputType;
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

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: two render branches times two variants times five saveOn triggers; branching is inherent to the primitive.
export function ActionInput(props: ActionInputProps): JSX.Element {
  const variant = props.variant ?? "single";
  const saveOn = props.saveOn ?? "blur";
  // "input" mode is a permanently-editable filter field — it never has a
  // view mode to toggle back to, so it starts in edit.
  const live = saveOn === "input";
  const [mode, setMode] = useState<"view" | "edit">(live ? "edit" : "view");
  const [draft, setDraft] = useState(props.value);
  const inputRef = useRef<HTMLInputElement | HTMLTextAreaElement | null>(null);

  useEffect(() => {
    if (mode === "view") setDraft(props.value);
  }, [props.value, mode]);

  useEffect(() => {
    // Don't steal focus on mount for a live filter field; only pull focus
    // when the user has explicitly toggled a view field into edit mode.
    if (mode === "edit" && !live && inputRef.current) {
      inputRef.current.focus();
      inputRef.current.select?.();
    }
  }, [mode, live]);

  const enterEdit = useCallback(() => {
    if (props.disabled) return;
    setDraft(props.value);
    setMode("edit");
  }, [props.disabled, props.value]);

  const commit = useCallback(
    (next: string) => {
      if (next !== props.value) {
        dispatchAction(props.action, { ...(props.actionData ?? {}), value: next });
      }
      // A live filter field stays editable; every other trigger returns
      // to view mode once the value is committed.
      if (!live) setMode("view");
    },
    [props.action, props.actionData, props.value, live]
  );

  const cancel = useCallback(() => {
    setDraft(props.value);
    if (!live) setMode("view");
  }, [props.value, live]);

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

  // Consumer data-*/aria-* forwarded onto whichever element is the root
  // for the current mode; the primitive's own attributes win on collision.
  const passthrough = collectPassthrough(props);

  if (mode === "view") {
    const rendered = props.renderView ? props.renderView(props.value) : props.value;
    const isEmpty = props.value.length === 0;
    return (
      // biome-ignore lint/a11y/useSemanticElements: <button> would swallow text selection and add default styling; div with role=button is the inline-edit idiom.
      <div
        {...passthrough}
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
    ...passthrough,
    class: `${classes["edit"]} ${classes["root"]}`,
    "data-polly-ui": true,
    "data-polly-action-input": true,
    "data-state": "editing",
    "data-variant": variant,
    placeholder: props.placeholder,
    value: draft,
    onInput: (e: JSX.TargetedEvent<HTMLInputElement | HTMLTextAreaElement>) => {
      const next = e.currentTarget.value;
      setDraft(next);
      if (live) commit(next);
    },
    onBlur: () => {
      if (saveOn === "blur") commit(draft);
      else if (!live) cancel();
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
      type={props.inputType ?? "text"}
      {...(common as unknown as JSX.HTMLAttributes<HTMLInputElement>)}
    />
  );
}
