# Team Task Manager - E2EE Local-First Collaboration

A production-quality example demonstrating **end-to-end encrypted, local-first team collaboration** with real-time sync.

## 🎯 What This Demonstrates

This example showcases advanced Polly patterns for building privacy-first collaborative applications:

- **🔐 End-to-End Encryption** - Server literally cannot read your data
- **💾 Local-First Architecture** - Works offline, syncs when online
- **👥 Real-Time Collaboration** - Team members see changes instantly
- **🔑 Key-as-Identity** - No traditional authentication needed
- **⚡ Reactive State** - UI updates automatically with Polly's `$sharedState`
- **🎯 Constraint Enforcement** - Business rules validated client + server side
- **🦀 Rust WASM Crypto** - High-performance encryption in the browser

## Architecture Overview

```
┌─────────────────────────────┐     ┌─────────────────────────────┐
│     Alice's Browser         │     │      Bob's Browser          │
│  ┌─────────────────────┐    │     │   ┌─────────────────────┐   │
│  │  IndexedDB          │    │     │   │  IndexedDB          │   │
│  │  (Local Storage)    │    │     │   │  (Local Storage)    │   │
│  │  ──────────────     │    │     │   │  ──────────────     │   │
│  │  tasks: [...]       │◄───┼─────┼───┤  tasks: [...]       │   │
│  │  workspace: {...}   │    │     │   │  workspace: {...}   │   │
│  └──────────▲──────────┘    │     │   └──────────▲──────────┘   │
│             │                │     │              │               │
│  ┌──────────┴──────────┐    │     │   ┌──────────┴──────────┐   │
│  │ Polly $sharedState  │    │     │   │ Polly $sharedState  │   │
│  │ (auto-persists &    │    │     │   │ (auto-persists &    │   │
│  │  syncs)             │    │     │   │  syncs)             │   │
│  └─────────┬───────────┘    │     │   └─────────┬───────────┘   │
│            │                 │     │             │                │
│  ┌─────────▼──────────┐     │     │   ┌─────────▼──────────┐    │
│  │ WASM Crypto Module │     │     │   │ WASM Crypto Module │    │
│  │ (Rust/ChaCha20)    │     │     │   │ (Rust/ChaCha20)    │    │
│  └────────────────────┘     │     │   └────────────────────┘    │
└─────────────┼────────────────┘     └──────────────┼──────────────┘
              │ WebSocket                           │
              │ (encrypted data only)               │
              └──────────┬────────────────────────┬─┘
                         │                        │
                    ┌────▼────────────────────────▼───┐
                    │   Elysia Server (Zero-Knowledge)│
                    │  ┌───────────────────────────┐  │
                    │  │ In-Memory State           │  │
                    │  │ (encrypted blobs only)    │  │
                    │  │                           │  │
                    │  │ Server CANNOT decrypt:   │  │
                    │  │ - Task text              │  │
                    │  │ - Comments               │  │
                    │  │ - User data              │  │
                    │  └───────────────────────────┘  │
                    └──────────────────────────────────┘
```

## Key Features

### 1. Zero-Knowledge Server

The server stores only encrypted blobs:

```typescript
// Server stores this:
{
  id: "task-123",
  encrypted: "iOjE3MDk1NjQwMDB9LCJzdGF0dXMiOiJ0b2R...", // Base64 ciphertext
  from: "alice-public-key",
  workspaceId: "workspace-abc"
}

// Server CANNOT see:
// - Task text: "Fix the login bug"
// - Description, priority, status, etc.
// - Any plaintext data
```

### 2. Local-First with Polly

All data stored locally with automatic persistence:

```typescript
// State automatically persists to IndexedDB
export const tasks = $sharedState<Task[]>("tasks", []);
export const workspace = $sharedState<Workspace | null>("workspace", null);

// Create task - stored locally immediately
tasks.value = [...tasks.value, newTask];

// Syncs to server when online (queued if offline)
api.createTask(encryptedTask);
```

### 3. Real-Time Collaboration

```typescript
// Alice creates a task
await createTask("Fix login bug", "high");

// Bob's client receives encrypted update via WebSocket
api.onMessage((data) => {
  if (data.type === "task_created") {
    // Decrypt with shared workspace key
    const task = await decryptTask(data.task.encrypted);
    // Polly automatically updates UI
    tasks.value = [...tasks.value, task];
  }
});
```

### 4. Business Constraints

Enforced both client and server-side:

```typescript
// Client-side: Prevent creation
if (priority === "urgent" && urgentTasks.length >= 3) {
  throw new Error("Maximum 3 urgent tasks allowed");
}

// Server-side: Validate before accepting
if (body.priority === "urgent") {
  const urgentCount = countUrgentTasks(workspaceId);
  if (urgentCount >= 3) {
    return { error: "Urgent task limit reached" };
  }
}
```

### 5. Key-Based Identity

No passwords, just cryptographic keypairs:

```typescript
// Generate identity
const keypair = await KeyPair.generate();
const user = {
  id: bytesToHex(keypair.publicKey), // Public key = User ID
  name: "Alice",
  publicKey: keypair.publicKey,
  privateKey: keypair.privateKey,
};

// Export for backup
const backup = exportUserKey(user);
// Save to file: alice-key.json
```

## Running the Example

### Prerequisites

- [Bun](https://bun.sh) 1.3+
- [mkcert](https://github.com/FiloSottile/mkcert) (required for HTTPS)
- [Rust](https://rustup.rs/) (for WASM crypto module, optional)

### Setup

```bash
# Navigate to example directory
cd examples/team-task-manager

# Install all dependencies (server + client)
bun install

# Generate SSL certificates (REQUIRED)
bun run setup:ssl

# Optional: Build Rust WASM module (falls back to Web Crypto API)
bun run build:crypto
```

**Why HTTPS is required:**
This example demonstrates end-to-end encryption, which requires secure connections. The setup script will:
- Detect if `mkcert` is installed
- Offer to install it via Homebrew if available
- Generate locally-trusted certificates for `localhost`
- Configure both server and client for HTTPS

Without SSL certificates, the servers will refuse to start.

### Development

**Option 1: Run both servers together** (recommended)
```bash
bun run dev
```

**Option 2: Run separately in different terminals**
```bash
# Terminal 1: Start server
bun run dev:server

# Terminal 2: Start client
bun run dev:client
```

Open **https://localhost:5173** in your browser

### Demo Workflow

1. **Create Your Identity**
   - Enter your name
   - Click "Generate Key"
   - Download backup (IMPORTANT!)

2. **Create Workspace**
   - Enter workspace name
   - Click "Create Workspace"

3. **Invite Team Members**
   - Click "👥 Invite"
   - Share the link with teammates
   - They can join and see all tasks (decrypted)

4. **Create Tasks**
   - Add task with priority
   - Teammates see it appear in real-time
   - Try urgent tasks (max 3!)

5. **Test Offline**
   - Disconnect network
   - Create tasks (stored locally)
   - Reconnect - tasks sync automatically!

## Code Highlights

### Encryption Layer

```typescript
// Task creation with encryption
export async function createTask(text: string, priority: Priority) {
  const task: Task = {
    id: crypto.randomUUID(),
    text,
    priority,
    // ... other fields
  };

  // Encrypt with workspace key
  const encrypted = await encryptText(
    JSON.stringify(task),
    workspace.value.workspaceKey
  );

  // Server gets only ciphertext
  await api.createTask(task.id, bytesToBase64(encrypted), userId, workspaceId);

  // Store plaintext locally
  tasks.value = [...tasks.value, task];
}
```

### Constraint Validation

```typescript
export function canCreateUrgentTask(): boolean {
  if (!workspace.value) return false;
  const urgentCount = tasks.value.filter(
    (t) => t.priority === "urgent" && t.status !== "done"
  ).length;
  return urgentCount < workspace.value.maxUrgentTasks;
}

// Used before creating urgent task
if (priority === "urgent" && !canCreateUrgentTask()) {
  throw new Error("Urgent task limit reached");
}
```

### Real-Time Sync

```typescript
// Set up WebSocket listener
useEffect(() => {
  const cleanup = api.onMessage("app", (data) => {
    switch (data.type) {
      case "task_created":
        handleIncomingTask(data.task); // Decrypts and adds to local state
        break;
      case "task_deleted":
        tasks.value = tasks.value.filter((t) => t.id !== data.taskId);
        break;
    }
  });

  return cleanup;
}, []);
```

## What Makes This Special

### 1. **True Zero-Knowledge**
The server is completely untrusted. Even if compromised, attackers get only encrypted blobs they can't decrypt.

### 2. **No Database Required**
Server is stateless (stores in memory). Clients have all data locally. Server just coordinates real-time sync.

### 3. **Offline-First**
Works completely offline. Queues changes and syncs when reconnected. No loading spinners!

### 4. **Production-Ready Patterns**
- Optimistic updates
- Conflict resolution
- Error handling
- Constraint validation
- Activity feed
- Role-based permissions

### 5. **Modern Tech Stack**
- Rust WASM for crypto
- Elysia + Bun for server
- Preact for UI
- Polly for state management
- Web Crypto API fallback

## Extending This Example

### Add More Constraints

```typescript
// Prevent completing tasks with unfinished dependencies
export function canCompleteTask(taskId: string): boolean {
  const task = getTaskById(taskId);
  if (!task) return false;

  return task.dependencies.every((depId) => {
    const dep = getTaskById(depId);
    return dep?.status === "done";
  });
}
```

### Add Approval Workflows

```typescript
export async function approveTask(taskId: string) {
  const task = getTaskById(taskId);
  if (task.createdBy === currentUser.value.id) {
    throw new Error("Cannot approve your own task");
  }

  await updateTask(taskId, { approvedBy: currentUser.value.id });
}
```

### Add Server-Side Persistence

```typescript
// server/src/db.ts
import { Database } from "bun:sqlite";

const db = new Database("workspace.db");

// Store encrypted tasks
db.exec(`
  CREATE TABLE IF NOT EXISTS encrypted_tasks (
    id TEXT PRIMARY KEY,
    encrypted TEXT,
    from_user TEXT,
    workspace_id TEXT,
    timestamp INTEGER
  )
`);
```

## Security Considerations

### ✅ What's Protected

- **Task content** - Encrypted with workspace key
- **Comments** - Encrypted with workspace key
- **User privacy** - Server never sees plaintext names

### ⚠️ What's NOT Protected (Metadata)

- **Task count** - Server knows how many tasks exist
- **Timing** - Server sees when tasks are created
- **Relationships** - Server sees which users are in which workspaces

### 🔒 Best Practices

1. **Backup Keys** - If you lose your key, data is gone forever
2. **Secure Key Storage** - Don't paste keys in Slack/email
3. **Use HTTPS** - Always use TLS in production
4. **Rotate Keys** - Generate new workspace keys periodically

## Comparison with Other Approaches

### vs Traditional Auth

| Traditional | Key-as-Identity |
|-------------|-----------------|
| Username + password | Cryptographic keypair |
| Server stores password hash | Server never sees private key |
| Password resets possible | No reset - backup critical |
| Trust the server | Zero-trust architecture |

### vs Firebase/Supabase

| Firebase | This Example |
|----------|--------------|
| Server reads all data | Server sees only ciphertext |
| Real-time database | Real-time + E2EE |
| Requires internet | Works offline |
| Vendor lock-in | Self-hosted option |

### vs Signal/Matrix

| Signal | This Example |
|--------|--------------|
| Messaging focus | Task management focus |
| Mobile-first | Web-first |
| Per-message encryption | Per-object encryption |
| Similar security model | Similar security model |

## Future Enhancements

- [ ] **Federation** - Connect multiple team servers
- [ ] **Multi-device sync** - One identity across devices
- [ ] **File attachments** - Encrypted file uploads
- [ ] **Audit logs** - Cryptographically signed events
- [ ] **Search** - Client-side encrypted search index
- [ ] **Mobile apps** - React Native version

## Learn More

- [Polly Documentation](../../README.md)
- [Local-First Software](https://www.inkandswitch.com/local-first/)
- [Signal Protocol](https://signal.org/docs/)
- [End-to-End Encryption](https://en.wikipedia.org/wiki/End-to-end_encryption)

## License

MIT
