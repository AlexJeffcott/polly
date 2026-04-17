import { expect, test } from "bun:test";
import { parseActionData } from "@fairfox/polly/actions";
import { createMockElement } from "@fairfox/polly/actions";

test("camelCases data-action-* attribute names", () => {
  const el = createMockElement({
    "data-action-text-set-id": "42",
    "data-action-variant-id": "3",
  });
  const result = parseActionData(el);
  expect(result).toEqual({ textSetId: "42", variantId: "3" });
});

test("ignores non data-action-* attributes", () => {
  const el = createMockElement({
    "data-action-value": "v",
    "data-other": "o",
    "aria-label": "x",
  });
  const result = parseActionData(el);
  expect(result).toEqual({ value: "v" });
});

test("returns an empty object when no matching attributes", () => {
  const el = createMockElement({ class: "thing", role: "button" });
  const result = parseActionData(el);
  expect(result).toEqual({});
});

test("preserves empty string values", () => {
  const el = createMockElement({ "data-action-value": "" });
  const result = parseActionData(el);
  expect(result).toEqual({ value: "" });
});
