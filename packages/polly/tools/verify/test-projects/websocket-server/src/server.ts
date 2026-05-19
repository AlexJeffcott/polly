// Test fixture: WebSocket server entry point
import { WebSocketServer } from "ws";
import type { ServerState } from "./types/state";

const server = new WebSocketServer({ port: 8080 });

const serverState: ServerState = {
  connections: 0,
  messages: [],
};

server.on("connection", (ws) => {
  serverState.connections++;

  ws.on("message", (data) => {
    serverState.messages.push(data.toString());
  });

  ws.on("close", () => {
    serverState.connections--;
  });
});
