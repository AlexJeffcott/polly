import { afterAll, describe, expect, test } from "bun:test";
import { WebSocketServer } from "ws";
import { resolveListenPort, resolveWebSocketPort } from "../ephemeral-port.ts";

const server = Bun.serve({ port: 0, fetch: () => new Response("ok") });
const wss = new WebSocketServer({ port: 0, host: "127.0.0.1" });
await new Promise<void>((resolve) => wss.once("listening", () => resolve()));
afterAll(async () => {
  server.stop(true);
  await new Promise<void>((resolve) => wss.close(() => resolve()));
});

describe("resolveListenPort", () => {
  test("reads the port off a host's `.server`", () => {
    expect(resolveListenPort({ server })).toBe(server.port ?? -1);
  });

  test("a host that is not listening, or no host, is a named failure", () => {
    for (const app of [{ server: null }, {}, null, 7]) {
      expect(() => resolveListenPort(app)).toThrow("resolveListenPort: app is not listening");
    }
  });
});

describe("resolveWebSocketPort", () => {
  test("reads the port off `address()`", () => {
    const address = wss.address();
    expect(resolveWebSocketPort(wss)).toBe(
      typeof address === "object" && address !== null ? address.port : -1
    );
  });

  test("a pipe address, or no server, is a named failure", () => {
    for (const value of [{ address: () => "/tmp/sock" }, {}, null]) {
      expect(() => resolveWebSocketPort(value)).toThrow(
        "resolveWebSocketPort: server is not listening on a TCP port"
      );
    }
  });
});
