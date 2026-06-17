import { describe, expect, test } from "bun:test";
import { orderCases } from "../../tools/test/src/tiers/order";
import type { CaseSpec } from "../../tools/test/src/tiers/types";

const c = (id: string, cost?: CaseSpec["cost"]): CaseSpec => ({
  id,
  cost,
  exec: { kind: "command", argv: ["true"] },
});

describe("orderCases", () => {
  test("default returns the input untouched (same reference)", () => {
    const input = [c("a", "light"), c("b", "heavy"), c("c")];
    expect(orderCases(input, "default")).toBe(input);
  });

  test("cost orders heaviest first, stable within equal weight", () => {
    const input = [c("a", "light"), c("b", "heavy"), c("c"), c("d", "heavy"), c("e", "light")];
    expect(orderCases(input, "cost").map((x) => x.id)).toEqual(["b", "d", "c", "a", "e"]);
  });

  test("fast orders lightest first, stable within equal weight", () => {
    const input = [c("a", "light"), c("b", "heavy"), c("c"), c("d", "heavy"), c("e", "light")];
    expect(orderCases(input, "fast").map((x) => x.id)).toEqual(["a", "e", "c", "b", "d"]);
  });

  test("unset cost sorts as medium, between light and heavy", () => {
    const input = [c("heavy", "heavy"), c("mid"), c("light", "light")];
    expect(orderCases(input, "cost").map((x) => x.id)).toEqual(["heavy", "mid", "light"]);
    expect(orderCases(input, "fast").map((x) => x.id)).toEqual(["light", "mid", "heavy"]);
  });

  test("does not mutate the input array", () => {
    const input = [c("a", "light"), c("b", "heavy")];
    const before = input.map((x) => x.id);
    orderCases(input, "cost");
    expect(input.map((x) => x.id)).toEqual(before);
  });
});
