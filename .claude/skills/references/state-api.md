# State Primitives API

## Table of Contents
- [Choosing a Primitive](#choosing-a-primitive)
- [$sharedState](#sharedstate)
- [$syncedState](#syncedstate)
- [$persistedState](#persistedstate)
- [$state](#state)
- [$serverState](#serverstate)
- [$peerState](#peerstate)
- [$meshState](#meshstate)
- [$resource](#resource)
- [Verification Mirror](#verification-mirror)

## Choosing a Primitive

| Primitive | Synced | Persisted | Use Case |
|-----------|--------|-----------|----------|
| `$sharedState` | Yes | Yes | Most common. Settings, user data, app state |
| `$syncedState` | Yes | No | Ephemeral shared state (UI selections, temp filters) |
| `$persistedState` | No | Yes | Local-only persistent (draft text, scroll position) |
| `$state` | No | No | Component-local ephemeral signals |
| `$serverState` | Yes | Yes | Server-side state (Elysia, Node.js) |
| `$peerState` | Yes (CRDT) | Yes | Server as peer; any device can rehydrate server |
| `$meshState` | Yes (CRDT) | Yes | Peer-to-peer only; server never sees data |
| `$resource` | No | No | Async data fetching with automatic re-fetch |

## $sharedState

```typescript
import { $sharedState } from '@fairfox/polly/state'

// Basic
const settings = $sharedState('app-settings', { theme: 'dark', notifications: true })

// With validation
import { validateShape } from '@fairfox/polly'
const settings = $sharedState('app-settings', defaultSettings, {
  validator: validateShape<Settings>({
    theme: 'string',
    notifications: 'boolean',
  }),
})

// With verification mirror
const loginState = $sharedState('login', { loggedIn: false }, { verify: true })
// loginState.verify is a plain object mirror for TLA+ verification
// loginState.verify.loggedIn automatically syncs with loginState.value.loggedIn
```

**Options:**
- `validator` - Runtime type guard function
- `verify` - When `true`, creates `.verify` plain-object mirror for TLA+
- `storage` - Custom StorageAdapter
- `sync` - Custom SyncAdapter
- `debounceMs` - Debounce for storage writes

**Usage:**
```typescript
// Read
const current = settings.value

// Write (triggers sync + persist automatically)
settings.value = { ...settings.value, theme: 'light' }

// Wait for hydration from storage
await settings.loaded
```

## $syncedState

Same API as `$sharedState` but NOT persisted to storage. State resets on restart.

```typescript
import { $syncedState } from '@fairfox/polly/state'
const filter = $syncedState<'all' | 'active' | 'done'>('filter', 'all')
```

## $persistedState

Same API as `$sharedState` but NOT synced across contexts. Each context has its own copy.

```typescript
import { $persistedState } from '@fairfox/polly/state'
const draftText = $persistedState('draft', '')
```

## $state

Local ephemeral signal. No key needed. No sync, no persist.

```typescript
import { $state } from '@fairfox/polly/state'
const isOpen = $state(false)
```

## $serverState

For server-side apps (Elysia, Node.js). Same API as `$sharedState`.

```typescript
import { $serverState } from '@fairfox/polly/state'
const authState = $serverState('auth', { loggedIn: false, userId: null }, { verify: true })
```

## $peerState

Automerge CRDT-backed state where every device (including the server) holds a full replica. If the server loses storage, any reconnecting client repopulates it through the normal Automerge sync protocol.

```typescript
import { createPeerStateClient, configurePeerState, $peerState } from '@fairfox/polly/peer'

// Client setup
const client = createPeerStateClient({ url: 'wss://yourapp.com/polly/peer' })
configurePeerState(client.repo)

const settings = $peerState('settings', { theme: 'dark' })
await settings.loaded
settings.value = { theme: 'light' } // syncs to all peers via Automerge
```

**Options on `createPeerStateClient`:**
- `url` — WebSocket URL of the peer repo server
- `sign` — When `true`, wraps the transport with MeshNetworkAdapter in sign-only mode (Ed25519, no encryption). Server can still parse sync messages.
- `keyring` — MeshKeyring for signing identity and known peers

**Server setup:**
```typescript
import { createPeerRepoServer } from '@fairfox/polly/peer'

const server = await createPeerRepoServer({ port: 3001, storagePath: './data' })
// server.repo is a full Automerge Repo — read/write docs from cron jobs, HTTP handlers, etc.
```

Or as an Elysia plugin:
```typescript
import { peerRepo } from '@fairfox/polly/elysia'
app.use(peerRepo())
// Access via context: pollyPeerRepo (Repo) and pollyPeerServer (server handle)
```

**Specialised variants:** `$peerText` (Automerge text), `$peerCounter` (Counter with delta), `$peerList` (array).

## $meshState

Automerge CRDT-backed state where peers exchange operations directly over WebRTC data channels. All operations are signed with Ed25519 and encrypted with XSalsa20-Poly1305. No server sees the data. A stateless signalling server helps peers discover each other.

```typescript
import { configureMeshState, $meshState, MeshNetworkAdapter, MeshWebRTCAdapter } from '@fairfox/polly/mesh'

const repo = new Repo({ network: [new MeshNetworkAdapter({ base: webrtcAdapter, keyring })] })
configureMeshState(repo)

const notes = $meshState('notes', { entries: [] })
// Operations flow peer-to-peer, signed and encrypted
```

**MeshKeyring interface:**
- `identity` — local peer ID
- `knownPeers` — Map of peerId → Ed25519 public key
- `documentKeys` — Map of keyId → symmetric document key
- `revokedPeers` — Set of revoked peer IDs
- `revocationAuthority?` — Ed25519 public key that can issue revocations

**Key exchange:** `createPairingToken()` / `applyPairingToken()` — base64-encoded binary token containing Ed25519 pubkey + symmetric doc key. Display as QR code for first-time device pairing.

**Revocation:** `createRevocation()` / `applyRevocation()` — signed revocation records that propagate to every peer. `revokePeerLocally()` for immediate local removal.

**Signalling server (Elysia):**
```typescript
import { signalingServer } from '@fairfox/polly/elysia'
app.use(signalingServer())
```

**Specialised variants:** `$meshText`, `$meshCounter`, `$meshList`.

## $resource

Async signal primitive that separates sync dependency tracking from async work. Solves the broken-tracking problem at `await` boundaries.

```typescript
import { $resource } from '@fairfox/polly'

const todos = $resource<{ userId: number | null }, Todo[]>('todos', {
  source: () => ({ userId: user.value?.id ?? null }),
  fetcher: async ({ userId }) => {
    if (userId === null) return []
    const res = await fetch(`/api/todos?userId=${userId}`)
    return res.json()
  },
  initialValue: [],
})
```

**Returns:** `Resource<TData>` with:
- `data` — `Signal<TData>` (initialValue before first success)
- `status` — `Signal<"idle" | "loading" | "success" | "error">`
- `error` — `Signal<Error | undefined>`
- `refetch()` — re-run fetcher with current source values

**Options:**
- `source` — synchronous function that reads signals (fully tracked)
- `fetcher` — async function receiving source output (must NOT read signals)
- `initialValue` — data value before first successful fetch

**Behavior:**
- Source output is deep-compared; identical values skip re-fetch
- Stale responses are discarded via generation counter (race-safe)
- When source changes, fetcher re-runs automatically

**Verification:** Each `$resource` emits three synthetic handlers (`{name}_FetchStart`, `{name}_FetchSuccess`, `{name}_FetchError`) modeling the fetch lifecycle as a state machine. Two state fields are auto-generated: `{name}_status` (enum) and `{name}_error` (boolean). These are auto-discovered when the resource file is in the analyzed tsconfig scope.

## Verification Mirror

When `{ verify: true }` is passed, the state gets a `.verify` property - a plain object that automatically mirrors the signal's value. This plain object is what the TLA+ analyzer reads.

```typescript
const loginState = $sharedState('login', { loggedIn: false, username: '' }, { verify: true })

// The .verify mirror auto-syncs:
loginState.value = { loggedIn: true, username: 'alice' }
// loginState.verify.loggedIn === true (automatically)

// Export for verification discovery:
export const state = loginState.verify
```

**Key rule:** State that participates in `requires()`/`ensures()` checks or `$constraints()` SHOULD use `{ verify: true }`.
