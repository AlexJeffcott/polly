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

### 2. [Minimal](./minimal)

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

### 3. [My Awesome Extension](./my-awesome-extension)

**Chrome extension with popup UI**

A simple extension with background service worker and popup interface.

**Features:**
- Background/popup architecture
- Reactive UI with Preact
- Cross-context messaging
- State persistence

**Great for:**
- Learning Chrome extension architecture
- Building simple extensions
- Understanding context boundaries

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

**Great for:**
- Understanding formal verification
- Learning TLA+ model checking
- Building production extensions
- Testing distributed state

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
- **Building a Chrome extension?** Try [My Awesome Extension](./my-awesome-extension)
- **Want to learn verification?** See [Todo List](./todo-list)
- **Need a reference?** Look at [Full Featured](./full-featured)

## Contributing Examples

We welcome new examples! Good examples:

- Demonstrate specific Polly features
- Include clear documentation
- Work out of the box
- Show real-world patterns
- Include tests (bonus: formal verification!)

See the [Contributing Guide](../CONTRIBUTING.md) for details.
