import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { ViewerServer } from "../viewer/server";

// Regression guard for polly#157: text assets must be served with an explicit
// charset=utf-8 so a non-ASCII glyph is not decoded as Latin-1 (mojibake).
describe("ViewerServer text responses carry charset=utf-8 (#157)", () => {
  const docsDir = mkdtempSync(join(tmpdir(), "polly-viewer-"));
  writeFileSync(join(docsDir, "architecture.dsl"), "workspace { /* ▶ */ }");
  const server = new ViewerServer({ docsDir, port: 0, open: false });
  const url = (path: string) => `http://127.0.0.1:${server.port}${path}`;

  beforeAll(() => server.start());
  afterAll(() => {
    server.stop();
    rmSync(docsDir, { recursive: true, force: true });
  });

  test("a server started on port 0 reports the port it was assigned", () => {
    expect(server.port).toBeGreaterThan(0);
  });

  test("main HTML page declares charset", async () => {
    const res = await fetch(url("/"));
    expect(res.headers.get("Content-Type")).toBe("text/html; charset=utf-8");
  });

  test("DSL source file declares charset", async () => {
    const res = await fetch(url("/architecture.dsl"));
    expect(res.headers.get("Content-Type")).toBe("text/plain; charset=utf-8");
    expect(await res.text()).toBe("workspace { /* ▶ */ }");
  });
});
