// WebSocket server entry point
// @ts-nocheck

import { WebSocketServer } from 'ws';
import type { RequestMessage } from './server/types';
import { routeMessage } from './server/handlers';

const wss = new WebSocketServer({ port: 8080 });

wss.on('connection', (ws) => {
  console.log('Client connected');

  ws.on('message', async (data) => {
    try {
      const message = JSON.parse(data.toString()) as RequestMessage;
      const response = await routeMessage(message);
      ws.send(response);
    } catch (error) {
      ws.send(JSON.stringify({ type: 'error', message: 'Invalid message format' }));
    }
  });

  ws.on('close', () => {
    console.log('Client disconnected');
  });
});

console.log('WebSocket server running on ws://localhost:8080');
