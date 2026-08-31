/**
 * Budget-margin reporting (polly#175).
 *
 * The point of the helper is that a case sitting just under its cap says so.
 * These cases pin the threshold behaviour at the boundary, because a helper
 * that quietly returns `undefined` at 99% would reintroduce exactly the
 * silence the issue was filed about.
 */
import { describe, expect, test } from "bun:test";
import { BUDGET_WARN_FRACTION, budgetUse, formatBudgetUse } from "../budget";

describe("budgetUse", () => {
  test("reports the fraction of the budget a case consumed", () => {
    expect(budgetUse(154_235, 180_000)).toBeCloseTo(0.8569, 4);
  });

  test("has nothing to report without a budget", () => {
    expect(budgetUse(1000, undefined)).toBeUndefined();
    expect(budgetUse(1000, 0)).toBeUndefined();
  });
});

describe("formatBudgetUse", () => {
  test("names the duty cycle and the budget for a case above the threshold", () => {
    // The run that crossed the line in polly#175, at its measured clean duration.
    expect(formatBudgetUse(154_235, 180_000)).toBe("86% of its 180000ms timeout budget");
  });

  test("stays quiet for a case with room to spare", () => {
    // The same case under the raised 300s budget.
    expect(formatBudgetUse(154_235, 300_000)).toBeUndefined();
    expect(formatBudgetUse(4_633, 180_000)).toBeUndefined();
  });

  test("speaks exactly at the threshold, not one tick after it", () => {
    const timeoutMs = 100_000;
    const atThreshold = timeoutMs * BUDGET_WARN_FRACTION;
    expect(formatBudgetUse(atThreshold, timeoutMs)).toBe("70% of its 100000ms timeout budget");
    expect(formatBudgetUse(atThreshold - 1, timeoutMs)).toBeUndefined();
  });

  test("keeps reporting past the budget — an overrun is not a silent pass", () => {
    expect(formatBudgetUse(210_000, 180_000)).toBe("117% of its 180000ms timeout budget");
  });
});
