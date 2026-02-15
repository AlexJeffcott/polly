# WebRTC P2P Chat - Polly Example

A peer-to-peer chat application demonstrating **direct browser-to-browser communication** using WebRTC data channels, with Polly managing local reactive state.

## What Makes This Different

Unlike other examples where data flows through the server, here the server is **only used for signaling** - actual chat messages travel directly between browsers via WebRTC!

```
Traditional (other examples):
Client A → Server → Client B

WebRTC P2P (this example):
Client A ←→ Client B (direct connection)
         ↓
      Server
  (signaling only)
```

## Features

- **Direct P2P messaging** - No server sees your chat messages
- **Real-time connections** - WebRTC data channels for instant delivery
- **Room-based** - Join rooms by ID to chat with specific groups
- **Connection state tracking** - See peer connection status and latency
- **Polly state management** - Reactive UI with `$syncedState`

## Architecture

```
┌─────────────────────────────┐     ┌─────────────────────────────┐
│     Alice's Browser         │     │      Bob's Browser          │
│  ┌─────────────────────┐    │     │   ┌─────────────────────┐   │
│  │ Polly State         │    │     │   │ Polly State         │   │
│  │ - peers             │    │     │   │ - peers             │   │
│  │ - messages          │    │     │   │ - messages          │   │
│  └──────────▲──────────┘    │     │   └──────────▲──────────┘   │
│             │                │     │              │               │
│  ┌──────────┴──────────┐    │     │   ┌──────────┴──────────┐   │
│  │ WebRTC DataChannel  │◄───┼─────┼───►│ WebRTC DataChannel  │   │
│  │ (Direct P2P)        │    │     │   │ (Direct P2P)        │   │
│  └─────────────────────┘    │     │   └─────────────────────┘   │
│             │                │     │              │               │
│  ┌──────────┴──────────┐    │     │   ┌──────────┴──────────┐   │
│  │ SignalingClient     │    │     │   │ SignalingClient     │   │
│  └─────────┬───────────┘    │     │   └─────────┬───────────┘   │
└────────────┼─────────────────┘     └─────────────┼───────────────┘
             │                                     │
             │  WebSocket (signaling only)         │
             └──────────┬──────────────────────────┘
                        │
                   ┌────▼──────────────┐
                   │ Signaling Server  │
                   │ (Elysia)          │
                   │                   │
                   │ • Relays SDP      │
                   │ • Relays ICE      │
                   │ • NO chat data!   │
                   └───────────────────┘
```

## Project Status

✅ **Complete and Functional!**

### Implemented
- ✅ Signaling server (Elysia + WebSocket)
- ✅ WebRTC peer connection management
- ✅ Data channel communication
- ✅ Polly reactive state management
- ✅ Room-based chat UI
- ✅ Connection status indicators
- ✅ Peer list with latency display
- ✅ Message delivery status

## Quick Start

### 1. Install Dependencies

```bash
cd examples/webrtc-p2p-chat
bun install
```

### 2. Start the Servers

```bash
# Run both server and client together
bun run dev
```

Or run separately in different terminals:

```bash
# Terminal 1: Signaling server
bun run --filter server dev    # Runs on http://localhost:3001

# Terminal 2: Client dev server
bun run --filter client dev    # Runs on http://localhost:5173
```

### 3. Test P2P Chat

1. **Open two browser windows/tabs**
   - Navigate to `http://localhost:5173` in both

2. **In Browser 1:**
   - Enter your name (e.g., "Alice")
   - Click "Generate" to create a room ID
   - Click "Join Room"

3. **In Browser 2:**
   - Enter your name (e.g., "Bob")
   - Copy the room ID from Browser 1
   - Click "Join Room"

4. **Chat away!**
   - Messages travel directly between browsers
   - Server never sees message content
   - Check connection status and latency

**Pro tip:** You can open multiple tabs in the same browser! Each tab acts as a separate peer with its own connection.

## UX & Testing

This example includes production-ready UX improvements:

- **One-Click Invites** - Copy shareable links with visual feedback
- **URL-Based Joining** - Click an invite link and join automatically
- **Welcoming Landing** - Clear value proposition for first-time visitors
- **Status Indicators** - Animated connection states and latency display
- **Empty States** - Helpful guidance when no peers or messages
- **Polished Design** - Modern gradients, animations, and transitions

For detailed testing instructions, see [TESTING.md](./TESTING.md).

For the complete list of UX improvements, see [UX_IMPROVEMENTS.md](./UX_IMPROVEMENTS.md).

## Available Commands

```bash
# Development
bun run dev                    # Run both server and client
bun run --filter server dev    # Server only
bun run --filter client dev    # Client only

# Type checking
bun run typecheck              # Check both server and client

# Build (for production)
bun run build
```

## How It Works

### 1. Signaling Phase

The server helps browsers find each other by relaying WebRTC signaling messages:

```typescript
// Client A creates an offer
const offer = await peerConnection.createOffer()
signalingClient.send({ type: 'offer', to: 'peer-b', offer })

// Server relays to Client B
roomManager.sendToPeer('peer-b', { type: 'offer', from: 'peer-a', offer })

// Client B creates answer
const answer = await peerConnection.createAnswer(offer)
signalingClient.send({ type: 'answer', to: 'peer-a', answer })

// ICE candidates also exchanged via server
```

### 2. P2P Connection Established

Once WebRTC negotiation completes, browsers connect directly:

```typescript
// Data channel is now open
dataChannel.send(JSON.stringify({
  type: 'chat_message',
  text: 'Hello!',
  timestamp: Date.now()
}))

// Server never sees this message!
```

### 3. Polly Manages Local State

State updates trigger reactive UI changes:

```typescript
// When message received over data channel
messages.value = [...messages.value, newMessage]

// UI automatically updates - no manual re-rendering needed!
```

## Key Concepts

### WebRTC Data Channels
- Binary or text data transfer
- Reliable (TCP-like) or unreliable (UDP-like) modes
- Encrypted by default (DTLS)
- No server involvement once connected

### Signaling Server
- Only handles connection setup
- Relays SDP offers/answers
- Relays ICE candidates
- Tracks room membership
- **Never sees actual messages**

### Polly State Management
- `$syncedState` - Syncs across components (local only, not network)
- `$state` - Ephemeral component state
- Automatic persistence to IndexedDB
- Reactive UI updates with Preact Signals

**Multi-Tab Behavior:**
- `displayName` uses `$syncedState` - persists so you don't re-enter it
- `peerId` uses `$state` - **ephemeral per-tab** so each tab is a separate peer
- This allows multiple tabs from the same browser to join the same room!

## Use Cases

This pattern is ideal for:
- **Chat applications** - Direct messaging without server storage
- **Gaming** - Low-latency game state updates
- **File transfer** - P2P file sharing
- **Collaborative tools** - Drawing, whiteboards, code editing
- **Video/audio** - Can add MediaStream tracks

## Comparison with Other Examples

| Feature | elysia-todo-app | team-task-manager | webrtc-p2p-chat |
|---------|----------------|-------------------|-----------------|
| Data flow | Client → Server → Client | Client → Server → Client | Client ↔ Client (direct) |
| Server role | Stores & syncs | Relays encrypted | Signaling only |
| Privacy | Server sees all | Server sees ciphertext | Server sees nothing |
| Offline | ✅ Works offline | ✅ Works offline | ❌ Needs peers online |
| Scalability | Good | Good | Excellent (no server load) |

## Learn More

- [WebRTC API Documentation](https://developer.mozilla.org/en-US/docs/Web/API/WebRTC_API)
- [Polly Framework](https://github.com/AlexJeffcott/polly)
- [Implementation Plan](./IMPLEMENTATION_PLAN.md)

## License

MIT
