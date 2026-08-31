# Polly examples

Each example is a self-contained app that exercises a different
combination of Polly's features. Pick whichever one most resembles
what you're building.

## Index

| Example | What it is |
|---------|------------|
| [minimal](./minimal) | The smallest Polly Chrome extension. Background script, popup, one piece of synced state, a TLA+ verification config. Start here if you're new. |
| [todo-list](./todo-list) | Chrome extension with login, CRUD, a 100-item cap, unit tests, and TLA+ verification of the handlers. Uses the `{ verify: true }` discovery pattern and subsystem-scoped verification. |
| [full-featured](./full-featured) | The largest example. Covers every Polly feature: multiple execution contexts, complex message flows, runtime constraints, `$sharedState` and `$persistedState` together, the full adapter stack. |
| [elysia-todo-app](./elysia-todo-app) | Full-stack web app using `@fairfox/polly/elysia`. Eden infers types end-to-end from the Elysia server, the client queues writes offline, and state syncs over WebSocket. Route-level authorization, declarative client effects. |
| [webrtc-p2p-chat](./webrtc-p2p-chat) | Browser-to-browser chat over WebRTC data channels. The server only handles signalling; message content never reaches it. Demonstrates room-based pairing and connection-state UI. |
| [blob-share](./blob-share) | Peer-to-peer file sharing over a real `MeshWebRTCAdapter`. Two tabs on one origin discover each other through a stateless signalling server and exchange encrypted, chunked, hash-verified files over a direct WebRTC data channel — the server never touches the bytes. Demonstrates `createBlobStore` and the `blob-have` → `blob-request` → `blob-chunk` pipeline. |
| [team-task-manager](./team-task-manager) | Collaborative task management with role-based access (`owner`/`admin`/`member`), `$constraints()` for workspace-gated operations, urgent-task counts as a verified numeric field, and parameter-traced task priority. Demonstrates the role-and-constraints pattern, not end-to-end encryption. |
| [mesh-recovery-pair](./mesh-recovery-pair) | Runnable demonstration of polly issue #103. Two werift mesh peers, one with a pre-populated `knownPeers` keyring and one freshly recovered, run against an in-process signalling server. Prints a wire-level transcript and a per-run sentinel that has to traverse the mesh. Toggles between the post-fix and pre-fix-emulated paths via `POLLY_103_DISABLE_FIX`. |

## Running an example

```bash
cd examples/<name>
bun install
bun run dev
```

Each example's README has the specific instructions: extensions load
their `dist/` directory in Chrome at `chrome://extensions`; web apps
boot through `bun run dev`; the WebRTC example needs the signalling
server running first.

## Picking one

- New to Polly: [minimal](./minimal).
- Building a Chrome extension: [todo-list](./todo-list) or [full-featured](./full-featured).
- Building a web app or PWA: [elysia-todo-app](./elysia-todo-app).
- Building a P2P / WebRTC app: [webrtc-p2p-chat](./webrtc-p2p-chat).
- Learning formal verification: [todo-list](./todo-list).
- Modelling roles and constraints: [team-task-manager](./team-task-manager).

## Contributing examples

Good examples are short, focused on one or two Polly features, and
work after `bun install && bun run dev` with no other setup. They
include a README that explains what the example demonstrates and how
to run it, and — where applicable — a `specs/verification.config.ts`
that the TLA+ pipeline can pick up.

An example that imports `@fairfox/polly/elysia` must pin the **same
`typescript` version as `packages/polly`** (currently `6.0.3`) in its
devDependencies. Elysia declares `typescript` as a peer dependency, so bun
installs one copy of Elysia per distinct `typescript` resolution. A workspace
on a different version gets a different Elysia, and
`new Elysia().use(signalingServer(...))` then fails to typecheck with
`TS2769 ... ElysiaAdapter is not assignable to ElysiaAdapter` naming two
`node_modules/.bun/elysia@<version>+<hash>` paths. The fix is to match the
version, not to cast the plugin to `any`.

Set `"types": ["bun"]` in an example's tsconfig, never `["bun-types"]` — the
package these workspaces depend on is `@types/bun`, and `bun-types` is not
installed anywhere in the repo. Pin `preact` and `@preact/signals` inside
polly's peer ranges too, or polly-ui components resolve to a second preact and
cannot be used as JSX.

Every example workspace with a tsconfig is typechecked by
`bun run check typecheck-examples` (part of `check all` and the `static` tier).
A new example is picked up from its tsconfig — nothing to register. Examples
typecheck against `packages/polly/dist`, so run `bun run build:lib` after
changing a polly type.

See [the contributing guide](../CONTRIBUTING.md) for the broader
workflow.
