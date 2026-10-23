import { describe, expect, test } from "bun:test";
import { readTheme } from "@/shared/state/app-state";

describe("readTheme", () => {
  test("returns each theme the settings select offers", () => {
    expect(readTheme("light")).toBe("light");
    expect(readTheme("dark")).toBe("dark");
    expect(readTheme("auto")).toBe("auto");
  });

  test("returns undefined for a value outside Settings['theme']", () => {
    expect(readTheme("sepia")).toBeUndefined();
    expect(readTheme("")).toBeUndefined();
  });
});
