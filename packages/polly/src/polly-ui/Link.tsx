/**
 * Link — token-styled navigational anchor.
 *
 * The primitive for plain hyperlinks: hub app-grid cards, a file
 * download, an external reference. <Button href> is for link-shaped
 * BUTTONS — a call to action wearing button chrome; <Link> is for
 * inline, textual links that read as links. `external` opens a new tab
 * with `rel="noopener noreferrer"`; `download` offers the target as a
 * file (an empty string keeps the resource's own filename).
 */

import type { ComponentChildren, JSX } from "preact";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";
import classes from "./Link.module.css";

export type LinkProps = PassthroughAttrs & {
  children: ComponentChildren;
  href: string;
  /** Open in a new tab with rel="noopener noreferrer". */
  external?: boolean;
  /** Offer the href as a download; an empty string keeps its filename. */
  download?: string;
  /** Drop the underline until hover — for link grids and card links. */
  subtle?: boolean;
  className?: string;
  id?: string;
};

export function Link(props: LinkProps): JSX.Element {
  const { children, href, external, download, subtle, className, id } = props;

  const parts = [classes["link"]];
  if (subtle) parts.push(classes["subtle"]);
  if (className) parts.push(className);

  return (
    <a
      {...collectPassthrough(props)}
      id={id}
      class={parts.filter(Boolean).join(" ")}
      href={href}
      target={external ? "_blank" : undefined}
      rel={external ? "noopener noreferrer" : undefined}
      download={download}
      data-polly-ui
      data-polly-link
    >
      {children}
    </a>
  );
}
