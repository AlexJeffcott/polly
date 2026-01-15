import { Elysia } from 'elysia';
import { cors } from '@elysiajs/cors';

/**
 * WebRTC P2P Chat - Signaling Server
 *
 * This server only handles signaling (helping peers find each other).
 * It NEVER sees actual chat messages - those travel directly P2P!
 */

const app = new Elysia()
  .use(cors())

  // Health check
  .get('/health', () => ({
    status: 'ok',
    uptime: process.uptime(),
    timestamp: Date.now()
  }))

  // WebSocket signaling endpoint (to be implemented)
  .ws('/signaling', {
    message(ws, message) {
      console.log('Received message:', message);
      // TODO: Implement signaling logic
    },

    close(ws) {
      console.log('WebSocket closed');
      // TODO: Cleanup peer connections
    }
  })

  .listen(3001);

console.log(`🎯 Signaling server running at ${app.server?.hostname}:${app.server?.port}`);
console.log(`   WebSocket: ws://${app.server?.hostname}:${app.server?.port}/signaling`);
