/**
 * Code — inline monospace code span.
 *
 * Renders a `<code>` with the `--polly-font-mono` stack, a faint sunken
 * tint, and snug padding so a consumer never hand-rolls a `.mono` class
 * for inline code, identifiers, or keyboard hints. For multi-line code
 * blocks, pass `block`, which switches to a pre-wrapped <pre><code>.
 */

import type { ComponentChildren, JSX } from "preact";
import classes from "./Code.module.css";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";

export type CodeProps = PassthroughAttrs & {
  children: ComponentChildren;
  /** Render as a block (<pre><code>) instead of an inline span. */
  block?: boolean;
  className?: string;
  id?: string;
};

export function Code(props: CodeProps): JSX.Element {
  const { children, block, className, id } = props;

  // Consumer data-*/aria-* spread first; the explicit attributes after
  // win on any collision.
  const passthrough = collectPassthrough(props);

  if (block) {
    const parts = [classes["block"]];
    if (className) parts.push(className);
    return (
      <pre
        {...passthrough}
        id={id}
        class={parts.filter(Boolean).join(" ")}
        data-polly-ui
        data-polly-code="block"
      >
        <code>{children}</code>
      </pre>
    );
  }

  const parts = [classes["code"]];
  if (className) parts.push(className);
  return (
    <code
      {...passthrough}
      id={id}
      class={parts.filter(Boolean).join(" ")}
      data-polly-ui
      data-polly-code="inline"
    >
      {children}
    </code>
  );
}
