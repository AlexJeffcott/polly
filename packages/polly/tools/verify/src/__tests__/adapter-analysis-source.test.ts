// The adapters' typescript-7 lifecycle: a caller's session or program is
// used and left open; with none, the adapter opens and closes its own.

import { afterAll, describe, expect, test } from "bun:test";
import path from "node:path";
import { AnalysisSession } from "../../../analysis/src/program";
import { detectAdapter } from "../adapters/detection";
import { selectAdapter } from "../adapters/registry";
import { WebSocketAdapter } from "../adapters/websocket";

const tsConfigPath = path.join(__dirname, "../../test-projects/websocket-server/tsconfig.json");

describe("adapter analysis source", () => {
  const session = new AnalysisSession();
  afterAll(() => session.close());

  test("a caller's session gives the same model as the adapter's own session", async () => {
    const adapter = new WebSocketAdapter({ tsConfigPath });
    const own = await adapter.extractModel();
    const shared = await adapter.extractModel(session);
    expect(shared).toEqual(own);
    expect(own.handlers.length).toBeGreaterThan(0);
  });

  test("the caller's session stays open and serves the same cached program", async () => {
    const before = await session.open(tsConfigPath);
    await detectAdapter(tsConfigPath, session);
    const adapter = await selectAdapter("generic", tsConfigPath, session);
    await adapter.extractModel(session);
    expect(await session.open(tsConfigPath)).toBe(before);
  });

  test("an open program is used as is", async () => {
    const program = await session.open(tsConfigPath);
    const fromProgram = await new WebSocketAdapter({ tsConfigPath }).extractModel(program);
    const fromSession = await new WebSocketAdapter({ tsConfigPath }).extractModel(session);
    expect(fromProgram).toEqual(fromSession);
  });

  test("a closed session is not reopened behind the caller's back", async () => {
    const closed = new AnalysisSession();
    await closed.close();
    await expect(new WebSocketAdapter({ tsConfigPath }).extractModel(closed)).rejects.toThrow(
      "AnalysisSession is closed"
    );
  });

  test("a missing tsconfig rejects from extractModel, not the constructor", async () => {
    const adapter = new WebSocketAdapter({ tsConfigPath: "/nonexistent/tsconfig.json" });
    await expect(adapter.extractModel()).rejects.toThrow("File not found");
  });
});
