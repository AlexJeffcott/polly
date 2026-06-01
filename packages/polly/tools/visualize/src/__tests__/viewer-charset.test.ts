import { describe, expect, test } from "bun:test";
import { ViewerServer } from "../viewer/server";

// Regression guard for polly#157: text assets must be served with an explicit
// charset=utf-8 so a non-ASCII glyph is not decoded as Latin-1 (mojibake).
describe("ViewerServer text responses carry charset=utf-8 (#157)", () => {
  const server = new ViewerServer({ docsDir: "/tmp", port: 0, open: false });
  // serve* helpers are private; reach them directly to assert headers without
  // binding a port.
  const reach = server as unknown as {
    serveMainPage(dsl: string): Response;
    serveDslFile(dsl: string): Response;
  };

  test("main HTML page declares charset", () => {
    const res = reach.serveMainPage("workspace {}");
    expect(res.headers.get("Content-Type")).toBe("text/html; charset=utf-8");
  });

  test("DSL source file declares charset", () => {
    const res = reach.serveDslFile("workspace { /* ▶ */ }");
    expect(res.headers.get("Content-Type")).toBe("text/plain; charset=utf-8");
  });
});
