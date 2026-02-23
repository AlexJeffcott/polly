# Team Task Manager Example

End-to-end encrypted, local-first task collaboration. The server stores only ciphertext — it cannot read task text, comments, or user data.

## What it demonstrates

- Zero-knowledge server: all data encrypted client-side before sending
- Local-first with `$sharedState`: works offline, syncs when reconnected
- Real-time collaboration via WebSocket broadcast of encrypted blobs
- Key-as-identity: public key = user ID, no passwords
- Polly Elysia middleware for offline queueing and optimistic updates
- `requires()` / `ensures()` contracts on task operations
- PWA: installable, service worker caching, persistent storage
- Optional Rust WASM crypto (ChaCha20-Poly1305), falls back to Web Crypto API

## Quick start

Prerequisites: [Bun](https://bun.sh) 1.3+, [mkcert](https://github.com/FiloSottile/mkcert) for HTTPS.

```bash
bun install
bun run setup:ssl     # generate localhost certificates (required)
bun run dev           # starts server + client
```

Open `https://localhost:5173`. Create an identity, create a workspace, invite others by sharing the link.

## How encryption works

Every task is encrypted with the workspace key before it leaves the client:

```typescript
export async function createTask(text: string, priority: Priority) {
  const task = { id: crypto.randomUUID(), text, priority, /* ... */ };

  const encrypted = await encryptText(JSON.stringify(task), workspace.value.workspaceKey);
  await api.createTask(task.id, bytesToBase64(encrypted), userId, workspaceId);

  tasks.value = [...tasks.value, task]; // plaintext stored locally
}
```

The server receives and relays only the ciphertext. Other clients in the workspace decrypt with the shared key.

## Handler contracts

Task operations use verification primitives:

```typescript
export function verifyCreateTask(text: string, priority: Priority) {
  requires(currentUser.value !== null, "Must be logged in");
  requires(workspace.value !== null, "Must have a workspace");
  requires(
    priority !== "urgent" || urgentTaskCount.value < workspace.value.maxUrgentTasks,
    "Urgent task limit not reached"
  );
  // ...
  ensures(tasks.value.length > 0, "Must have at least one task");
}
```

Run `bun run verify` from the client directory to model-check these contracts.

## File structure

```
server/
  src/index.ts              Elysia server with polly() middleware (offline, broadcast)
client/
  src/
    state.ts                $sharedState for tasks, workspace, user
    handlers.ts             Verification contracts (requires/ensures)
    tasks.ts                Task CRUD with encryption
    api.ts                  Eden treaty client (type-safe from server)
    crypto.ts               Web Crypto API / WASM fallback
    workspace.ts            Workspace + key management
    network.ts              Online/offline status signals
    pwa.ts                  Install prompt, service worker registration
    components/             UI components
  specs/
    verification.config.ts  TLA+ verification bounds
    constraints.ts          State constraints
shared/
  types.ts                  Domain types shared between server and client
crypto/
  src/lib.rs                Rust ChaCha20-Poly1305 (optional WASM module)
```

## Next steps

- [elysia-todo-app](../elysia-todo-app/) — simpler full-stack example without encryption
- [todo-list](../todo-list/) — Chrome extension with subsystem-scoped verification
