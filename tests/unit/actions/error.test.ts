import { beforeEach, expect, test } from "bun:test";
import {
  clearError,
  errorState,
  setError,
  submitError,
} from "@fairfox/polly/actions";

beforeEach(() => {
  clearError();
});

test("setError appends to errorState with default severity error", () => {
  const id = setError("Boom");
  expect(errorState.value.length).toBe(1);
  const entry = errorState.value[0];
  expect(entry?.id).toBe(id);
  expect(entry?.message).toBe("Boom");
  expect(entry?.severity).toBe("error");
  expect(entry?.createdAt).toBeGreaterThan(0);
});

test("setError honours severity and action options", () => {
  setError("Slowed down", { severity: "warning", action: "sync:pull" });
  const entry = errorState.value[0];
  expect(entry?.severity).toBe("warning");
  expect(entry?.action).toBe("sync:pull");
});

test("clearError by id removes one entry", () => {
  const idA = setError("A");
  setError("B");
  clearError(idA);
  expect(errorState.value.map((e) => e.message)).toEqual(["B"]);
});

test("clearError with no id clears all", () => {
  setError("A");
  setError("B");
  clearError();
  expect(errorState.value).toEqual([]);
});

test("submitError records the action and derives message from an Error", () => {
  submitError("team:submit", new Error("conflict"));
  const entry = errorState.value[0];
  expect(entry?.message).toBe("conflict");
  expect(entry?.action).toBe("team:submit");
  expect(entry?.severity).toBe("error");
});

test("submitError coerces non-Error values via String()", () => {
  submitError("team:submit", "string failure");
  expect(errorState.value[0]?.message).toBe("string failure");
});
