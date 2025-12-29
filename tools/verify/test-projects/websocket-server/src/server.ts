// Test fixture: WebSocket server entry point
import { WebSocketServer } from 'ws';
import type { ServerState, ClientState } from './types/state';

const server = new WebSocketServer({ port: 8080 });

let serverState: ServerState = {
  connections: 0,
  messages: [],
};

server.on('connection', (ws) => {
  serverState.connections++;

  ws.on('message', (data) => {
    serverState.messages.push(data.toString());
  });

  ws.on('close', () => {
    serverState.connections--;
  });
});
