// A fixed details column for the exported Structurizr site.
//
// Structurizr opens the tooltip at the pointer, so a long property list covers
// the boxes next to the one under the pointer. This style reserves a column at
// the right of the page and opens every tooltip in it. The diagram fits to the
// left of the column, because Structurizr reads the diagram width from
// #diagram, which the margin narrows.

export const DETAILS_PANEL_WIDTH_PX = 400;

const MARKER = "polly-details-panel";

export const DETAILS_PANEL_STYLE = `<style id="${MARKER}">
body::after { content: "Hover a box or an arrow to see its details here."; position: fixed; top: 0; right: 0; bottom: 0; width: ${DETAILS_PANEL_WIDTH_PX}px; box-sizing: border-box; padding: 16px; border-left: 1px solid #cccccc; background: #f6f6f6; color: #666666; font: 14px sans-serif; z-index: 5; }
#diagram { margin-right: ${DETAILS_PANEL_WIDTH_PX}px; }
#tooltip { position: fixed !important; top: 0 !important; right: 0 !important; bottom: 0 !important; left: auto !important; width: ${DETAILS_PANEL_WIDTH_PX}px !important; max-width: none !important; margin: 0 !important; box-sizing: border-box; border-radius: 0 !important; overflow-y: auto; pointer-events: none; z-index: 6 !important; }
</style>`;

/**
 * Returns the site's index.html with the details-panel style at the end of its
 * head. A page that already holds the style comes back unchanged.
 */
export function withDetailsPanel(html: string): string {
  if (html.includes(`id="${MARKER}"`)) {
    return html;
  }
  const headEnd = html.indexOf("</head>");
  if (headEnd === -1) {
    throw new Error("The exported index.html has no </head>, so the details panel has no place.");
  }
  return `${html.slice(0, headEnd)}${DETAILS_PANEL_STYLE}\n${html.slice(headEnd)}`;
}
