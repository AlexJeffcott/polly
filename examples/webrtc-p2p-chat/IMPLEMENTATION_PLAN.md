# WebRTC P2P Chat - Implementation Plan

## Overview

This example demonstrates **peer-to-peer communication** using WebRTC data channels, with Polly managing local state reactively. Unlike the other examples where data flows through the server, here the server is **only used for signaling** - actual messages travel directly between browsers.

## Architecture

```
┌─────────────────────────────┐     ┌─────────────────────────────┐
│     Alice's Browser         │     │      Bob's Browser          │
│  ┌─────────────────────┐    │     │   ┌─────────────────────┐   │
│  │  Polly State        │    │     │   │  Polly State        │   │
│  │  - peers            │    │     │   │  - peers            │   │
│  │  - messages         │    │     │   │  - messages         │   │
│  └──────────▲──────────┘    │     │   └──────────▲──────────┘   │
│             │                │     │              │               │
│  ┌──────────┴──────────┐    │     │   ┌──────────┴──────────┐   │
│  │ PeerManager         │    │     │   │ PeerManager         │   │
│  │ - Manages WebRTC    │    │     │   │ - Manages WebRTC    │   │
│  └──────────┬──────────┘    │     │   └──────────┬──────────┘   │
│             │                │     │              │               │
│  ┌──────────┴──────────┐    │     │   ┌──────────┴──────────┐   │
│  │ WebRTC DataChannel  │◄───┼─────┼───┤ WebRTC DataChannel  │   │
│  │ (Direct P2P)        │    │     │   │ (Direct P2P)        │   │
│  └─────────────────────┘    │     │   └─────────────────────┘   │
│             │                │     │              │               │
│  ┌──────────┴──────────┐    │     │   ┌──────────┴──────────┐   │
│  │ SignalingClient     │    │     │   │ SignalingClient     │   │
│  │ (WebSocket)         │    │     │   │ (WebSocket)         │   │
│  └─────────┬───────────┘    │     │   └─────────┬───────────┘   │
└────────────┼─────────────────┘     └─────────────┼───────────────┘
             │                                     │
             │  (Only signaling messages)          │
             └──────────┬────────────────────────┬─┘
                        │                        │
                   ┌────▼────────────────────────▼───┐
                   │   Elysia Server (Signaling)    │
                   │  ┌───────────────────────────┐  │
                   │  │ Room Manager              │  │
                   │  │ - Tracks peers in rooms   │  │
                   │  │ - Relays SDP/ICE          │  │
                   │  │ - NO message data!        │  │
                   │  └───────────────────────────┘  │
                   └──────────────────────────────────┘
```

## Key Differences from Other Examples

| Example | Data Flow | Server Role | Use Case |
|---------|-----------|-------------|----------|
| **elysia-todo-app** | Client → Server → Client | Stores & syncs data | Traditional web app |
| **team-task-manager** | Client → Server → Client | Relays encrypted data | Collaborative docs |
| **webrtc-p2p-chat** | Client ↔ Client (direct) | Signaling only | Chat, gaming, files |

**Key insight:** The server in this example NEVER sees message content - it only helps browsers find each other and establish direct connections.

## Project Structure

```
examples/webrtc-p2p-chat/
├── package.json              # Workspace root
├── README.md                 # User-facing documentation
├── IMPLEMENTATION_PLAN.md    # This file
├── .gitignore
│
├── server/                   # Signaling server (minimal)
│   ├── package.json
│   ├── tsconfig.json
│   └── src/
│       ├── index.ts          # Main server with WebSocket
│       ├── room-manager.ts   # Room and peer management
│       └── types.ts          # Signaling message types
│
└── client/                   # Preact frontend
    ├── package.json
    ├── tsconfig.json
    ├── index.html
    └── src/
        ├── main.tsx          # Entry point
        ├── App.tsx           # Main app component
        ├── state.ts          # Polly state management
        ├── types.ts          # Shared types
        │
        ├── components/
        │   ├── RoomLobby.tsx        # Join/create room UI
        │   ├── ChatRoom.tsx         # Main chat interface
        │   ├── PeerList.tsx         # Connected peers list
        │   ├── MessageList.tsx      # Chat messages
        │   └── ConnectionStatus.tsx # Network status indicator
        │
        └── webrtc/
            ├── signaling-client.ts   # WebSocket signaling
            ├── peer-manager.ts       # Manage multiple peer connections
            ├── peer-connection.ts    # Single RTCPeerConnection wrapper
            └── data-channel.ts       # RTCDataChannel with typed messages
```

## Type Definitions

### Signaling Messages (server/src/types.ts)

```typescript
// Messages sent between client and server for WebRTC signaling
export type SignalingMessage =
  // Room management
  | { type: 'join_room'; roomId: string; peerId: string; displayName: string }
  | { type: 'leave_room'; roomId: string; peerId: string }

  // Peer discovery
  | { type: 'room_joined'; roomId: string; peers: PeerInfo[] }
  | { type: 'peer_joined'; peer: PeerInfo }
  | { type: 'peer_left'; peerId: string }

  // WebRTC signaling
  | { type: 'offer'; from: string; to: string; offer: RTCSessionDescriptionInit }
  | { type: 'answer'; from: string; to: string; answer: RTCSessionDescriptionInit }
  | { type: 'ice_candidate'; from: string; to: string; candidate: RTCIceCandidateInit }

export interface PeerInfo {
  id: string;
  displayName: string;
  joinedAt: number;
}
```

### Data Channel Messages (client/src/types.ts)

```typescript
// Messages sent P2P over WebRTC data channels
export type P2PMessage =
  | { type: 'chat_message'; id: string; text: string; timestamp: number; from: string }
  | { type: 'typing_indicator'; isTyping: boolean; from: string }
  | { type: 'ping'; timestamp: number }
  | { type: 'pong'; timestamp: number }

export interface Peer {
  id: string;
  displayName: string;
  connectionState: RTCPeerConnectionState;
  latency?: number; // ms, calculated from ping/pong
  connectedAt: number;
}

export interface ChatMessage {
  id: string;
  text: string;
  from: string;
  fromName: string;
  timestamp: number;
  delivered: boolean;
}

export interface Room {
  id: string;
  joinedAt: number;
}
```

## Implementation Steps

### Phase 1: Project Setup
- [x] Create directory structure
- [ ] Write package.json files (workspace setup)
- [ ] Configure TypeScript
- [ ] Add basic .gitignore
- [ ] Write initial README

### Phase 2: Server (Signaling)
- [ ] Implement types (SignalingMessage, PeerInfo)
- [ ] Create RoomManager class
  - Track rooms and peers
  - Handle join/leave
  - Relay signaling messages
- [ ] Build Elysia server with WebSocket
- [ ] Add health check endpoint
- [ ] Test with multiple connections

### Phase 3: Client - WebRTC Layer
- [ ] Create SignalingClient
  - WebSocket connection management
  - Message serialization
  - Reconnection logic
- [ ] Implement PeerConnection class
  - RTCPeerConnection wrapper
  - Data channel setup
  - Offer/answer/ICE handling
- [ ] Build PeerManager
  - Manage multiple peer connections
  - Handle signaling messages
  - Route P2P messages
- [ ] Add ping/pong for latency measurement

### Phase 4: Client - State Management
- [ ] Define Polly state ($syncedState)
  - currentRoom
  - peers
  - messages
  - displayName, peerId
- [ ] Connect PeerManager to state
  - Update peers array on connection changes
  - Add messages to state
  - Trigger UI updates

### Phase 5: Client - UI Components
- [ ] RoomLobby component
  - Name input
  - Room ID input with generate button
  - Join/create room
- [ ] ChatRoom component
  - Layout with sidebar
  - Message input form
- [ ] PeerList component
  - Show connected peers
  - Connection state indicators
  - Latency display
- [ ] MessageList component
  - Scrolling message list
  - Message delivery status
  - Timestamp formatting
- [ ] ConnectionStatus component
  - Signaling connection status
  - P2P connection count

### Phase 6: Styling & Polish
- [ ] Add CSS (simple, clean design)
- [ ] Loading states
- [ ] Error handling UI
- [ ] Responsive design
- [ ] Dark mode (optional)

### Phase 7: Documentation
- [ ] Comprehensive README
  - Architecture explanation
  - WebRTC concepts
  - Running instructions
  - Screenshots/demo
- [ ] Code comments
- [ ] Type documentation

### Phase 8: Testing (Optional)
- [ ] Server tests (room management)
- [ ] Client unit tests
- [ ] Integration tests (signaling flow)

## Key Concepts to Demonstrate

### 1. WebRTC Fundamentals

**Signaling vs Data Channels:**
```typescript
// Signaling: Server helps browsers find each other
signalingClient.send({ type: 'offer', to: peerId, offer })

// Data Channel: Direct browser-to-browser communication
dataChannel.send(JSON.stringify({ type: 'chat_message', text: 'Hello!' }))
```

### 2. Connection Flow

```
1. Alice joins room "abc123"
   → Server tells Alice about existing peers

2. Alice creates offer for Bob
   → Server relays offer to Bob

3. Bob creates answer
   → Server relays answer to Alice

4. ICE candidates exchanged
   → Server relays candidates

5. Connection established!
   → Alice and Bob now connected directly
   → Server no longer involved in communication
```

### 3. Polly for Local State

```typescript
// State automatically persists and updates UI
export const peers = $syncedState<Peer[]>('peers', [])
export const messages = $syncedState<ChatMessage[]>('messages', [])

// IMPORTANT: Multi-tab design decision
export const displayName = $syncedState<string>('displayName', '')  // Persisted
export const peerId = $state<string>(crypto.randomUUID())            // Per-tab!

// Why peerId is per-tab:
// - Each browser tab = separate peer with unique WebRTC connections
// - Allows multiple tabs to join the same room
// - Prevents ID conflicts in signaling server

// When peer connects:
peers.value = [...peers.value, newPeer]  // UI auto-updates!

// When message received:
messages.value = [...messages.value, newMessage]  // UI auto-updates!
```

### 4. Mesh Network Pattern

With N peers:
- Each peer connects to N-1 other peers
- Total connections: N * (N-1) / 2
- Example: 4 peers = 6 connections

```
    A
   /|\
  / | \
 B--+--C
  \ | /
   \|/
    D
```

## Production Considerations

### NAT Traversal
- Currently uses free STUN servers (Google)
- Production needs TURN servers for ~10% of connections
- Services: Twilio, xirsys, or self-hosted coturn

### Scalability
- Mesh works well for 2-6 peers
- Beyond 8 peers, consider SFU (Selective Forwarding Unit)
- Or switch to MCU (Multipoint Control Unit)

### Security
- Add encryption layer on data channels
- Implement message authentication
- Rate limiting on signaling server

### Reliability
- Handle peer disconnections gracefully
- Reconnection logic
- Message acknowledgments/retry

## Feature Extensions

### Phase 9: Enhanced Features (Future)
- [ ] File transfer over data channels
- [ ] Typing indicators
- [ ] Read receipts
- [ ] User presence (online/away)
- [ ] Message history persistence (IndexedDB)
- [ ] Multiple rooms per user
- [ ] Private messages (1-on-1 channels)

### Phase 10: Advanced Features (Future)
- [ ] Video/audio tracks
- [ ] Screen sharing
- [ ] Collaborative canvas/whiteboard
- [ ] E2E encryption
- [ ] Message reactions
- [ ] User avatars

## Testing Strategy

### Manual Testing
1. Open two browser windows
2. Join same room with different names
3. Send messages back and forth
4. Close one window, verify cleanup
5. Test with 3+ peers

### Automated Testing
- Mock WebSocket for signaling tests
- Mock RTCPeerConnection for WebRTC tests
- Integration tests with real server

## Success Criteria

✅ Two browsers can connect via WebRTC
✅ Messages sent appear in both browsers instantly
✅ Server only sees signaling messages, not content
✅ Polly state management makes UI reactive
✅ Connection state clearly indicated
✅ Clean disconnect handling
✅ Comprehensive documentation

## Learning Outcomes

After implementing this example, developers will understand:

1. **WebRTC mechanics** - How browsers establish P2P connections
2. **Signaling patterns** - Server role in connection establishment
3. **Data channels** - Sending arbitrary data P2P
4. **Connection management** - ICE, SDP, state machines
5. **Polly for local state** - Reactive UI without server sync
6. **Network topologies** - Mesh vs star vs hybrid
7. **NAT traversal** - Why STUN/TURN servers are needed

## Comparison with Other Examples

### Similar to team-task-manager
- Real-time collaboration
- Multiple connected clients
- Reactive state updates

### Different from team-task-manager
- **No server storage** - Server holds zero data
- **Direct P2P** - Messages don't touch server
- **No encryption needed** - Browser-to-browser is already encrypted (DTLS)
- **Different scale** - Mesh limits peer count

### Complements elysia-todo-app
- Shows alternative architecture pattern
- Demonstrates when P2P makes sense
- Different trade-offs (latency vs server load)

## Next Steps

Ready to implement! Should we:
1. Start with server implementation (signaling)?
2. Begin with client WebRTC layer?
3. Build UI components first?
4. Set up project configuration?

Your preference?
