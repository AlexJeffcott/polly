/**
 * Html — render trusted, already-sanitised raw markup.
 *
 * The deliberate escape hatch for the rare thing polly-ui cannot
 * express: a locally generated, already-safe SVG (a QR code), a
 * pre-rendered diagram. The caller owns safety — `html` goes straight
 * into `dangerouslySetInnerHTML`, so it MUST be trusted or sanitised
 * first. For untrusted markdown use `renderMarkdown`, which sanitises;
 * for anything a primitive already covers, use the primitive.
 */

import { createElement, type JSX } from "preact";
import { collectPassthrough, type PassthroughAttrs } from "./internal/passthrough.ts";

export type HtmlProps = PassthroughAttrs & {
  /** Trusted, already-sanitised HTML. The caller owns its safety. */
  html: string;
  /** Polymorphic wrapper element (div, span, figure, …). Defaults to 'div'. */
  as?: keyof JSX.IntrinsicElements;
  className?: string;
  id?: string;
};

export function Html(props: HtmlProps): JSX.Element {
  const { html, as = "div", className, id } = props;

  return createElement(as, {
    // Consumer data-*/aria-*/title first; the primitive's own
    // attributes below win on any collision.
    ...collectPassthrough(props),
    id,
    class: className,
    "data-polly-ui": true,
    "data-polly-html": true,
    dangerouslySetInnerHTML: { __html: html },
  });
}
