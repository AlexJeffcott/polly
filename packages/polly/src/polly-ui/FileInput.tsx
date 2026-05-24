/**
 * FileInput — a styled trigger for the native file picker.
 *
 * A file is a binary object: it cannot ride a `data-action` attribute
 * the way a string value does, so FileInput is the one input primitive
 * that takes a callback. `onFiles` fires with the chosen FileList. The
 * native <input type="file"> stays in the DOM — visually hidden inside
 * the <label> — so the whole control opens the picker and remains
 * keyboard-accessible (polly#135).
 */

import type { JSX } from "preact";
import classes from "./FileInput.module.css";

export type FileInputProps = {
  /** Fired with the chosen files whenever the selection changes. */
  onFiles: (files: FileList) => void;
  /** Visible trigger text. Default: 'Choose file'. */
  label?: string;
  /** `accept` filter forwarded to the native input (e.g. 'image/*'). */
  accept?: string;
  /** Allow selecting more than one file. */
  multiple?: boolean;
  disabled?: boolean;
  className?: string;
  id?: string;
};

export function FileInput(props: FileInputProps): JSX.Element {
  const { onFiles, label = "Choose file", accept, multiple, disabled, className, id } = props;

  const handleChange = (e: JSX.TargetedEvent<HTMLInputElement>): void => {
    const { files } = e.currentTarget;
    if (files && files.length > 0) onFiles(files);
  };

  const parts = [classes["fileInput"]];
  if (disabled) parts.push(classes["disabled"]);
  if (className) parts.push(className);

  return (
    <label id={id} class={parts.filter(Boolean).join(" ")} data-polly-ui data-polly-file-input>
      <input
        type="file"
        class={classes["native"]}
        accept={accept}
        multiple={multiple}
        disabled={disabled}
        onChange={handleChange}
      />
      <span>{label}</span>
    </label>
  );
}
