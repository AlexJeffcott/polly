# Polly Examples

This directory contains complete example applications demonstrating Polly's capabilities.

## Examples

### 1. [Elysia Todo App](./elysia-todo-app) - **NEW!** 🎉

**Full-stack web app with Elysia + Bun**

A complete todo application demonstrating Polly's Elysia middleware integration for building distributed web applications.

**Features:**
- Zero type duplication (Eden infers from Elysia)
- Offline-first with automatic queueing
- Real-time sync via WebSocket broadcast
- Route-level authorization
- Declarative client effects
- Production-ready (minimal overhead)

**Great for:**
- Learning how SPAs are distributed systems
- Building offline-first web apps
- Understanding CAP theorem in practice
- Real-time collaborative applications

[View example →](./elysia-todo-app)

---

### 2. [WebRTC P2P Chat](./webrtc-p2p-chat) - **NEW!** 🎉

**Peer-to-peer chat with WebRTC data channels**

A real-time chat application demonstrating direct browser-to-browser communication using WebRTC, with the server only handling signaling.

**Features:**
- Direct P2P messaging (server never sees content)
- WebRTC data channels
- Room-based chat
- Connection status and latency monitoring
- Polly reactive state for local UI management
- Signaling server (Elysia + WebSocket)

**Great for:**
- Learning WebRTC fundamentals
- Understanding P2P architectures
- Building privacy-first applications
- Low-latency real-time communication

[View example →](./webrtc-p2p-chat)

---

### 3. [Minimal](./minimal)

**Chrome extension starter**

The simplest possible Polly extension. Great starting point for understanding the basics.

**Features:**
- Single background script
- Basic message handling
- State synchronization
- TLA+ verification setup

**Great for:**
- First-time Polly users
- Understanding core concepts
- Quick prototyping

---

### 4. [Todo List](./todo-list)

**Chrome extension with formal verification**

A complete todo list extension with both traditional testing and TLA+ verification.

**Features:**
- User authentication
- Full CRUD operations
- 100 todo limit enforcement
- Unit tests + TLA+ verification
- Framework double-execution prevention
- **NEW:** Verified state discovery pattern (`{ verify: true }`)

**Great for:**
- Understanding formal verification
- Learning TLA+ model checking
- Building production extensions
- Testing distributed state
- Multi-tab PWAs and WebSocket apps (via verified state handlers)

---

### 5. [Full Featured](./full-featured)

**Complete Chrome extension showcase**

The most comprehensive example showing all Polly features.

**Features:**
- Multiple execution contexts
- Complex message flows
- Advanced state management
- Production-grade architecture

**Great for:**
- Advanced Polly users
- Large-scale extensions
- Reference architecture

---

### 6. [Team Task Manager](./team-task-manager)

**Collaborative task management with role constraints**

A multi-user task management application demonstrating Polly's state management with role-based access control and formal verification.

**Features:**
- Workspace and task state with `{ verify: true }`
- Role-based authorization (owner, admin, member)
- Urgent task count tracking (`{ type: "number" }`)
- `$constraints()` for workspace-gated operations
- Parameter tracing for task priority

**Great for:**
- Role-based access patterns
- Complex domain modeling with verification
- Understanding `$constraints()` usage
- Team collaboration patterns

---

## Quick Start

Each example has its own README with detailed instructions. Generally:

```bash
cd examples/<example-name>
bun install
bun run dev
```

## Choosing an Example

- **New to Polly?** Start with [Minimal](./minimal)
- **Building a web app?** Check out [Elysia Todo App](./elysia-todo-app)
- **Building P2P/WebRTC apps?** Try [WebRTC P2P Chat](./webrtc-p2p-chat)
- **Want to learn verification?** See [Todo List](./todo-list)
- **Need a reference?** Look at [Full Featured](./full-featured)
- **Building team tools?** See [Team Task Manager](./team-task-manager)

## Contributing Examples

We welcome new examples! Good examples:

- Demonstrate specific Polly features
- Include clear documentation
- Work out of the box
- Show real-world patterns
- Include tests (bonus: formal verification!)

See the [Contributing Guide](../CONTRIBUTING.md) for details.
