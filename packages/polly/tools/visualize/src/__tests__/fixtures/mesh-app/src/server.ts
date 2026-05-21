// Mesh chat server entry point — a fixture for the polly#114 visualiser.
// @ts-nocheck

import { WebSocketServer } from "ws";
import { routeMessage } from "./server/handlers";
import type { RequestMessage } from "./server/types";

const wss = new WebSocketServer({ port: 8080 });

wss.on("connection", (ws) => {
  ws.on("message", async (data) => {
    const message = JSON.parse(data.toString()) as unknown as RequestMessage;
    const response = await routeMessage(message);
    ws.send(response);
  });
});

console.log("Mesh chat server running on ws://localhost:8080");
