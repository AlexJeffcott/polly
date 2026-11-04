import { describe, expect, test } from "bun:test";
import { DETAILS_PANEL_STYLE, withDetailsPanel } from "../runner/details-panel";

const page = '<html><head><title>t</title></head><body><div id="diagram"></div></body></html>';

describe("withDetailsPanel", () => {
  test("puts the style at the end of the head", () => {
    expect(withDetailsPanel(page)).toBe(
      `<html><head><title>t</title>${DETAILS_PANEL_STYLE}\n</head><body><div id="diagram"></div></body></html>`
    );
  });

  test("leaves a page that already holds the style unchanged", () => {
    const once = withDetailsPanel(page);
    expect(withDetailsPanel(once)).toBe(once);
  });

  test("refuses a page with no head end", () => {
    expect(() => withDetailsPanel("<body></body>")).toThrow("no </head>");
  });
});
