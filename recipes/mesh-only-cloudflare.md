# mesh-only-cloudflare

> I want to deploy a Polly mesh app — the server is not on the data path
> — on a free Cloudflare tier.

Static HTML and JS go to Cloudflare Pages. The signalling relay runs as a
Cloudflare Worker with a single Durable Object for the peer map. Both
sides fit inside the free plans for small teams; the data itself never
touches Cloudflare, only the brief SDP/ICE exchange during peer
discovery.

## Why Cloudflare

Mesh state pays almost nothing to keep online. The only live piece is
the signalling relay, and the relay only sees traffic during the seconds
that peers are establishing or re-establishing connections. A Worker
with one Durable Object is the smallest correct answer: stateful enough
to hold the peer map across requests, cheap enough to sit idle for long
stretches.

You need a Cloudflare account, `wrangler` installed (`bun add -g
wrangler` or the installer on Cloudflare's docs), and a Polly app that
already runs against a localhost signalling server through
`createMeshClient`. If you are starting from zero, the
`actions-driven-app` guide gets you to a running client; come back here
to deploy it.

## The signalling Worker

Durable Objects let one running instance hold the peer-id → WebSocket
map for every active pairing handshake in progress. Requests route to
the object by name; Cloudflare keeps it alive for the duration of its
open connections and hibernates it when the last socket closes.

Create `worker/src/index.ts`:

```ts
export class SignalingRoom {
  private peers = new Map<string, WebSocket>();

  constructor(private state: DurableObjectState) {}

  async fetch(request: Request): Promise<Response> {
    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    server.accept();

    let myPeerId: string | null = null;

    server.addEventListener("message", (event) => {
      let msg: { type: string; peerId?: string; targetPeerId?: string; payload?: unknown };
      try {
        msg = JSON.parse(event.data as string);
      } catch {
        return;
      }

      if (msg.type === "join" && msg.peerId) {
        myPeerId = msg.peerId;
        this.peers.set(myPeerId, server);
        return;
      }

      if (msg.type === "signal" && msg.targetPeerId) {
        const target = this.peers.get(msg.targetPeerId);
        if (!target) {
          server.send(JSON.stringify({
            type: "error", reason: "unknown-target", targetPeerId: msg.targetPeerId,
          }));
          return;
        }
        target.send(JSON.stringify(msg));
      }
    });

    server.addEventListener("close", () => {
      if (myPeerId) this.peers.delete(myPeerId);
    });

    return new Response(null, { status: 101, webSocket: client });
  }
}

export default {
  async fetch(request: Request, env: { ROOM: DurableObjectNamespace }): Promise<Response> {
    const upgrade = request.headers.get("Upgrade");
    if (upgrade !== "websocket") return new Response("expected websocket", { status: 426 });

    // One global room for small teams. Split by URL path for multi-tenant.
    const id = env.ROOM.idFromName("default");
    const room = env.ROOM.get(id);
    return room.fetch(request);
  },
};
```

This is the whole relay. The wire protocol mirrors the Elysia
signalling plugin's — `{type: "join", peerId}` to register, `{type:
"signal", peerId, targetPeerId, payload}` to relay. Polly's
`MeshSignalingClient` speaks this protocol out of the box; you do not
wire anything new on the client.

Minimal `worker/wrangler.toml`:

```toml
name = "polly-signaling"
main = "src/index.ts"
compatibility_date = "2026-04-01"

[[durable_objects.bindings]]
name = "ROOM"
class_name = "SignalingRoom"

[[migrations]]
tag = "v1"
new_classes = ["SignalingRoom"]
```

`wrangler deploy` inside `worker/` publishes the Worker at
`https://polly-signaling.<your-subdomain>.workers.dev`. Upgrade requests
to the root path get routed into the Durable Object.

## The client

`createMeshClient` takes the Worker URL as its signalling target. The
rest is what any browser app needs: a keyring persisted through a
storage adapter, IndexedDB for document bytes so reloads do not lose
data.

```ts
import { createMeshClient } from "@fairfox/polly/mesh";
import { IndexedDBStorageAdapter } from "@automerge/automerge-repo-storage-indexeddb";
import { indexedDbKeyringStorage } from "./keyring-storage";

const keyring = { storage: indexedDbKeyringStorage("polly-keyring") };

const client = await createMeshClient({
  signaling: {
    url: "wss://polly-signaling.your-subdomain.workers.dev/",
    peerId: crypto.randomUUID(),
  },
  keyring,
  repoStorage: new IndexedDBStorageAdapter("polly-docs"),
});
```

`indexedDbKeyringStorage` is a four-method implementation of
`KeyringStorage` (`load`, `save`, `clear` plus the serialiser). Write it
once against IndexedDB; the types in `@fairfox/polly/mesh` describe the
exact shape.

Two peers on different devices will not find each other until they
pair. Polly's `createPairingToken` / `applyPairingToken` is the path:
one device mints a short-lived token (typically shown as a QR code or a
pasteable string), the other device applies it on arrival. Neither the
signalling Worker nor Cloudflare ever sees the symmetric document key —
the token carries it, end-to-end.

Wire the pairing UX in the application — a button that opens a modal,
shows the token, accepts a token from the other side. That is reader
work; it lives in your action registry next to the rest of your domain.

## Static hosting

Any static build tool lands here — Vite, Bun's built-in HTML bundler,
esbuild, Parcel. The only thing Cloudflare Pages cares about is a
directory of files. Running `wrangler pages deploy dist` (or whatever
your build output folder is called) uploads it and prints a URL.

The two deploys are independent. Worker and Pages do not need to share
a project; the client reads the Worker URL from a build-time env var or
a config file you ship alongside the HTML.

## Free-tier envelope

Cloudflare's free Workers plan includes 100,000 requests per day and
generous Durable Object limits for a small team. The signalling Worker
handles a few requests per peer per handshake, then goes quiet — with
ten users on stable connections, the daily request count usually stays
under a thousand.

The scale-out points that matter:

- **More than ~50 concurrent active pairings**: one Durable Object per
  room stops scaling. Partition by a tenant id in the DO name.
- **Multi-region latency**: Cloudflare picks the nearest DC per
  request, but the DO itself lives in one region. Teams distributed
  across continents may see handshake delays of a few hundred
  milliseconds. Normal WebRTC handshakes are two to three round trips,
  so budget accordingly.
- **Exceeding the free plan**: Workers Paid is five dollars a month and
  covers orders of magnitude more traffic. The architectural story does
  not change.

## What this guide deliberately doesn't cover

Your own HTML, your own CSS, how your app boots — all reader work. The
recipe stops at "the signalling Worker is live and the client can talk
to it". Everything above the Polly surface is application code you
compose on top.

Authentication of pairing tokens lives outside Polly too — a token
authorises a peer, but deciding which users are allowed to hand one out
is your system's decision. A common answer: protect the pairing UI
behind login, treat a paired peer as trusted for that user's documents.

## Follow-ups worth knowing

If your team outgrows one Durable Object room, the `signalingServer`
plugin for Elysia (in `@fairfox/polly/elysia`) runs on any Node/Bun
host and has the same protocol. Move there when latency or tenancy
starts to matter; the client is unchanged.

For an always-on archival peer — a device that is always online,
participates in sync, and gives lone users a reliable syncing partner
— see `recipes/mesh-pi-peer.md`.
