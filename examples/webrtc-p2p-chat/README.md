# WebRTC P2P Chat Example

Peer-to-peer chat over WebRTC data channels. The server handles signaling only — actual messages travel directly between browsers.

## What it demonstrates

- WebRTC data channels for direct browser-to-browser communication
- Signaling server (Elysia + WebSocket) that never sees chat content
- Polly state primitives for local-only reactive state
- Per-tab identity: `$syncedState` for display name, `$state` for ephemeral peer ID

```
Client A ---- WebRTC data channel ---- Client B
    \                                    /
     \---- signaling (SDP/ICE) only ---/
                    |
              Elysia Server
```

## Quick start

```bash
bun install
bun run dev
```

This starts the signaling server on `http://localhost:3001` and the client on `http://localhost:5173`.

To test:
1. Open two browser tabs at `http://localhost:5173`
2. Enter a name in each, generate a room ID in one tab, paste it in the other
3. Join the room — messages travel directly between tabs, never through the server

## Architecture

```
┌─────────────────────────┐     ┌─────────────────────────┐
│   Alice's Browser       │     │    Bob's Browser        │
│                         │     │                         │
│   Polly State           │     │   Polly State           │
│   ($syncedState,        │     │   ($syncedState,        │
│    $state)              │     │    $state)              │
│         │               │     │         │               │
│   WebRTC DataChannel ◄──┼─────┼──► WebRTC DataChannel   │
│         │               │     │         │               │
│   SignalingClient       │     │   SignalingClient       │
└─────────┼───────────────┘     └─────────┼───────────────┘
          │  WebSocket (signaling only)   │
          └───────────┬───────────────────┘
                      │
               Signaling Server
               (relays SDP/ICE,
                never sees messages)
```

## State design

Polly manages local UI state only — it does not sync data over the network in this example. WebRTC handles that.

```typescript
// client/src/state.ts
const currentRoom = $syncedState<Room | null>("currentRoom", null);   // persisted
const displayName = $syncedState<string>("displayName", "");          // persisted
const peerId     = $state<string>(crypto.randomUUID());               // ephemeral, per-tab
const messages   = $syncedState<ChatMessage[]>("messages", []);       // persisted
const peers      = $syncedState<Peer[]>("peers", []);                 // synced across components
```

`displayName` uses `$syncedState` so you don't re-enter it on reload. `peerId` uses `$state` so each tab is a separate peer — multiple tabs from the same browser can join the same room.

## File structure

```
server/
  src/
    index.ts              Elysia signaling server (WebSocket at /signaling)
    room-manager.ts       Room and peer tracking
    types.ts              Signaling message types
client/
  src/
    state.ts              Polly state primitives
    App.tsx               Chat UI
    components/           ChatRoom, MessageList, PeerList
    webrtc/
      signaling-client.ts WebSocket connection to signaling server
      peer-connection.ts  WebRTC negotiation and data channels
      peer-manager.ts     Coordinates signaling + P2P connections
  specs/
    verification.config.ts TLA+ verification bounds
```

## Next steps

- [elysia-todo-app](../elysia-todo-app/) — full-stack with Elysia middleware and server-side state
- [team-task-manager](../team-task-manager/) — end-to-end encryption with zero-knowledge server
