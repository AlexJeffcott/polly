/**
 * Markdown rendering for ActionInput's view mode.
 *
 * Ship a ready-made `renderMarkdown` that consumers pass to the
 * `renderView` prop of <ActionInput>. Parses the value with `marked`
 * and sanitises the HTML with `DOMPurify`, then inlines the result via
 * `dangerouslySetInnerHTML`. Both libraries are optional peer deps of
 * @fairfox/polly — they only ship in the bundles of apps that import
 * this subpath.
 *
 * ```tsx
 * import { ActionInput } from "@fairfox/polly/ui";
 * import { renderMarkdown } from "@fairfox/polly/ui/markdown";
 *
 * <ActionInput value={note.body} action="note:update" variant="multi" renderView={renderMarkdown} />
 * ```
 */

import DOMPurify from "dompurify";
import { marked } from "marked";
import type { JSX } from "preact";

export function renderMarkdown(value: string): JSX.Element {
  const html = marked.parse(value, { async: false }) as string;
  const clean = DOMPurify.sanitize(html);
  return <div dangerouslySetInnerHTML={{ __html: clean }} />;
}
