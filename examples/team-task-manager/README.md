# Team Task Manager - E2EE Local-First Collaboration

A production-quality example demonstrating **end-to-end encrypted, local-first team collaboration** with real-time sync.

## 🎯 What This Demonstrates

This example showcases advanced Polly patterns for building privacy-first collaborative applications:

- **🔐 End-to-End Encryption** - Server literally cannot read your data
- **💾 Local-First Architecture** - Works offline, syncs when online
- **👥 Real-Time Collaboration** - Team members see changes instantly
- **🔑 Key-as-Identity** - No traditional authentication needed
- **📱 Multi-Device Sync** - Export/import your key to use on multiple devices
- **📲 Progressive Web App** - Install on any device, full offline support
- **⚡ Reactive State** - UI updates automatically with Polly's `$sharedState`
- **🎯 Constraint Enforcement** - Business rules validated client + server side
- **🦀 Rust WASM Crypto** - High-performance encryption in the browser
- **🛡️ Eden Treaty + Polly** - Production-grade type-safe API with offline-first middleware

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

5. **Multi-Device Sync**
   - Click "Export Key" to download your identity
   - Open app on another device/browser
   - Click "Import Existing Key"
   - Paste your key - all workspaces sync automatically!

6. **Test Offline**
   - Disconnect network
   - Create tasks (stored locally)
   - Reconnect - tasks sync automatically!

7. **Install as App (PWA)**
   - Look for "Install App" prompt (bottom right)
   - Or use browser menu: "Install Team Task Manager"
   - App runs standalone with faster load times
   - Full offline support with service worker

## Progressive Web App Features

This example is a fully-featured PWA with:

### 📲 Installability
- **One-click install** - Install prompt appears automatically
- **Standalone mode** - Runs like a native app
- **App shortcuts** - Quick access to common actions
- **Works on all platforms** - Desktop, mobile, tablet

### 🔄 Offline Support
- **Service worker** - Caches app shell and assets
- **Background sync** - Queues changes when offline
- **Smart caching** - Cache-first for assets, network-first for API
- **Persistent storage** - Data won't be evicted

### ⚡ Performance
- **Instant loading** - Loads from cache
- **Smooth updates** - Background updates with user prompt
- **Optimistic UI** - Updates appear immediately

### 🔔 Notifications (Coming Soon)
- Push notifications for task updates
- Background updates when app is closed

To test the PWA features:
```bash
# Start the app
bun run dev

# Open in browser
open https://localhost:5173

# Check PWA features in DevTools
# Chrome: Application > Manifest / Service Workers
# Firefox: Debugger > Service Workers
```

## Eden Treaty + Polly Middleware

This example demonstrates production-grade patterns using Eden treaty for type-safe APIs and Polly middleware for offline-first behavior.

### Server-Side Configuration

```typescript
import { Elysia } from "elysia";
import { polly } from "@fairfox/polly/elysia";

const app = new Elysia()
  .use(
    polly({
      // Offline configuration - automatic queuing and optimistic updates
      offline: {
        "POST /api/tasks": {
          queue: true,
          optimistic: (body) => ({
            success: true,
            taskId: body.id,
          }),
          merge: "replace",
        },
        "PATCH /api/tasks/:id": {
          queue: true,
          merge: "replace",
        },
      },

      // Effects - broadcast changes to connected clients
      effects: {
        "POST /api/tasks": {
          broadcast: true,
        },
        "PATCH /api/tasks/:id": {
          broadcast: true,
        },
      },

      // Custom WebSocket path for real-time sync
      websocketPath: "/polly/ws",
    })
  )

  // Normal Elysia routes - no Polly annotations needed!
  .post("/api/tasks", ({ body }) => {
    // Your regular handler code
    return { success: true, taskId: body.id };
  });

// Export type for Eden treaty client
export type App = typeof app;
```

### Client-Side Usage

```typescript
import { treaty } from "@elysiajs/eden";
import type { App } from "../../server/src/index";

// Create type-safe client - types automatically inferred!
const client = treaty<App>(API_URL);

// Wrap in class for cleaner API
export class APIClient {
  async createTask(id: string, encrypted: string, from: string, workspaceId: string) {
    const { data, error } = await client.api.tasks.post({
      id,
      encrypted,
      from,
      workspaceId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }
}
```

### Key Benefits

1. **Zero Type Duplication** - Eden generates types from Elysia automatically
2. **Centralized Offline Config** - All offline behavior defined in middleware
3. **Automatic Broadcasting** - Real-time updates configured declaratively
4. **Optimistic Updates** - Server sends optimistic responses for offline queuing
5. **Clean Separation** - Route handlers stay simple, Polly handles distributed systems concerns

## Polly Framework Patterns

This example uses Polly's patterns for state management and testing:

### Network State Management

```typescript
// network.ts - Polly-style reactive signals
import { signal, computed } from "@preact/signals-core";

export const isOnline = signal(navigator.onLine);
export const isSyncing = signal(false);
export const pendingSync = signal(0);

export const syncStatus = computed(() => {
  if (!isOnline.value) {
    return pendingSync.value > 0
      ? `Offline - ${pendingSync.value} changes pending`
      : "Offline";
  }
  if (isSyncing.value) {
    return `Syncing ${pendingSync.value} changes...`;
  }
  return "Online";
});
```

### Test Utilities

```typescript
// Tests use Polly's mock adapters
import { createMockFetch } from "@fairfox/polly/test";

test("API client works", async () => {
  const mockFetch = createMockFetch();
  global.fetch = mockFetch.fetch;

  // Queue mock response
  mockFetch._responses.push({
    json: async () => ({ success: true }),
  });

  await api.createTask(...);

  // Verify call was made
  expect(mockFetch._calls.length).toBe(1);
});
```

### State with Polly

```typescript
// Using Polly's $sharedState for persistence + sync
import { $sharedState } from "@fairfox/polly/state";

export const tasks = $sharedState<Task[]>("tasks", []);
export const workspace = $sharedState<Workspace | null>("workspace", null);

// Automatically persisted to IndexedDB
// Automatically synced across contexts in Chrome extensions
```

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

### PWA Service Worker

```typescript
// Service worker automatically caches app assets
self.addEventListener('fetch', (event) => {
  const { request } = event;

  // Cache-first strategy for app assets
  event.respondWith(
    caches.match(request).then((cachedResponse) => {
      if (cachedResponse) {
        // Return cached version immediately
        return cachedResponse;
      }

      // Fetch from network and cache
      return fetch(request).then((response) => {
        caches.open(CACHE_NAME).then((cache) => {
          cache.put(request, response.clone());
        });
        return response;
      });
    })
  );
});
```

### Install Prompt

```typescript
// main.tsx - Set up install prompt
setupInstallPrompt((prompt) => {
  console.log("Install prompt is available");
});

// InstallPrompt component - Show install UI
export function InstallPrompt() {
  const handleInstall = async () => {
    const result = await showInstallPrompt();
    if (result === 'accepted') {
      console.log('App installed!');
    }
  };

  return (
    <button onClick={handleInstall}>
      📱 Install App
    </button>
  );
}
```

## What Makes This Special

### 1. **True Zero-Knowledge**
The server is completely untrusted. Even if compromised, attackers get only encrypted blobs they can't decrypt.

### 2. **No Database Required**
Server is stateless (stores in memory). Clients have all data locally. Server just coordinates real-time sync.

### 3. **Offline-First**
Works completely offline. Queues changes and syncs when reconnected. No loading spinners!

### 4. **Progressive Web App**
- Installable on any device (desktop, mobile, tablet)
- Full offline support with service worker
- Fast loading from cache
- Persistent storage prevents data loss
- Works like a native app

### 5. **Production-Ready Patterns**
- Optimistic updates
- Conflict resolution
- Error handling
- Constraint validation
- Activity feed
- Role-based permissions

### 6. **Modern Tech Stack**
- **Eden Treaty** - Type-safe end-to-end API (zero duplication)
- **Polly Middleware** - Offline-first patterns with declarative config
- **Rust WASM** - High-performance crypto in browser
- **Elysia + Bun** - Fast, modern server runtime
- **Preact** - Lightweight reactive UI
- **Service Worker** - Full offline support
- **$sharedState** - Automatic persistence and sync

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

- [ ] **File attachments** - Encrypted file uploads
- [ ] **Audit logs** - Cryptographically signed events
- [ ] **Search** - Client-side encrypted search index
- [ ] **Push notifications** - Real-time notifications when app is closed

## Learn More

- [Polly Documentation](../../README.md)
- [Local-First Software](https://www.inkandswitch.com/local-first/)
- [Signal Protocol](https://signal.org/docs/)
- [End-to-End Encryption](https://en.wikipedia.org/wiki/End-to-end_encryption)

## License

MIT
