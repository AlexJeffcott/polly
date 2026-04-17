# mesh-pi-peer

> I want a Raspberry Pi to participate as a trusted always-on peer on
> my Polly mesh.

An always-on peer changes the shape of a mesh app. Without one, two
users are both offline most of the time, and edits only merge when the
two devices happen to be on together. With a Pi on the LAN (or anywhere
with a public IP), every peer has a reliable sync partner, writes
propagate within seconds, and the archival copy lets you restore a
freshly installed device without pairing across multiple others.

## What you are building

A Pi running a small Bun process that holds a Polly `MeshClient`, a
file-backed keyring, and a file-backed Automerge-Repo storage adapter.
On boot it loads the keyring, opens its signalling connection, accepts
WebRTC connections from authorised peers, and syncs every document it
knows about. systemd keeps it running.

You need a Pi 3 or better (512 MB RAM is the floor), Raspberry Pi OS
Lite or any modern Debian, Bun 1.3+, and network reachability to your
signalling server. The signalling Worker from
`mesh-only-cloudflare.md` works, as does any Elysia app running the
`signalingServer` plugin.

## WebRTC on Node

Browsers ship `RTCPeerConnection`; Node does not. Two options, both
supported peer-deps on Polly:

**werift** is a pure-TypeScript WebRTC implementation. Installs
everywhere, runs on ARMv7 and ARM64 without native bindings, DataChannel
throughput is fine for document sync. The Pi recipe picks this one
because Pi arch portability matters.

**@roamhq/wrtc** wraps libwebrtc with C++ bindings. Faster for
high-bandwidth use, but the published prebuilts do not reliably cover
ARMv7 and lag behind Node releases. Reach for it on x86_64 servers
where throughput is the bottleneck; skip it on Pi.

```sh
bun add @fairfox/polly tweetnacl werift
bun add @automerge/automerge @automerge/automerge-repo
```

## Identity and pairing

A fresh Pi has no keyring. `bootstrapCliKeyring` does the first-run
dance: generate an Ed25519 identity, print the fingerprint, wait for a
pairing token on stdin, apply it, save. On every subsequent run the
same call loads the saved keyring and returns.

```ts
import { createMeshClient } from "@fairfox/polly/mesh";
import { bootstrapCliKeyring, fileKeyringStorage } from "@fairfox/polly/mesh/node";
import { NodeFSStorageAdapter } from "@automerge/automerge-repo-storage-nodefs";
import { RTCPeerConnection } from "werift";

const storage = fileKeyringStorage("/var/lib/polly/keyring.json");
const keyring = await bootstrapCliKeyring({ storage });

const client = await createMeshClient({
  signaling: {
    url: "wss://polly-signaling.your-subdomain.workers.dev/",
    peerId: `pi-${keyring.identity.fingerprint.slice(0, 8)}`,
  },
  rtc: { RTCPeerConnection },
  keyring,
  repoStorage: new NodeFSStorageAdapter("/var/lib/polly/docs"),
});

console.log(`mesh peer online, peerId ${client.signaling.peerId}`);
await new Promise(() => {}); // run forever
```

Save as `/opt/polly-peer/peer.ts`. The first time you run it, the
process prints the fingerprint and blocks on stdin:

```
Polly mesh-state CLI bootstrap
──────────────────────────────
Fingerprint:  9f:2c:14:a8:de:11:63:80

Authorise this peer on a trusted device (open the pairing UI, enter
the fingerprint above, copy the generated token). Then paste the
pairing token below and press enter.
```

On your laptop, open the app, enter that fingerprint into the pairing
UI, copy the generated token, paste it into the Pi's terminal, press
enter. The Pi writes its keyring to disk. Subsequent boots skip this.

## systemd service

```ini
# /etc/systemd/system/polly-peer.service
[Unit]
Description=Polly mesh peer
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
User=polly
Group=polly
WorkingDirectory=/opt/polly-peer
ExecStart=/home/polly/.bun/bin/bun run /opt/polly-peer/peer.ts
Restart=on-failure
RestartSec=10
StandardInput=null
StandardOutput=journal
StandardError=journal

[Install]
WantedBy=multi-user.target
```

`StandardInput=null` matters: systemd must not feed the service stdin,
or the one-shot pairing flow will read EOF and throw on every boot
after the first. Once the keyring exists, `bootstrapCliKeyring` returns
without touching stdin at all.

Enable and start:

```sh
sudo useradd --system --home /var/lib/polly --create-home polly
sudo mkdir -p /var/lib/polly/docs /opt/polly-peer
sudo chown -R polly:polly /var/lib/polly /opt/polly-peer
sudo cp peer.ts /opt/polly-peer/
sudo systemctl daemon-reload
sudo systemctl enable polly-peer
```

Do not start it yet — the first run needs stdin for pairing. Instead:

```sh
sudo -u polly /home/polly/.bun/bin/bun run /opt/polly-peer/peer.ts
# paste the token when prompted, wait for "Pairing applied", Ctrl+C
sudo systemctl start polly-peer
```

After that, `systemctl status polly-peer` and `journalctl -u polly-peer
-f` are your operational hooks.

## Hardware minimums

Pi 3 and Pi 3+ with 1 GB RAM run comfortably for small meshes (a
handful of documents, up to five or six paired peers). Pi Zero 2 W
works but memory pressure climbs as the document set grows. Anything
older than Pi 3 is not worth the trouble — werift's TypeScript runtime
overhead compounds with the platform's lack of cycles.

Storage: `/var/lib/polly/docs` grows with the mesh. Automerge's binary
format is compact (changes are compacted on save), but budget a few
hundred megabytes if you expect heavy usage over a year. A cheap
tmpfiles.d rotation of old sync-state snapshots keeps it lean.

## Backups

The keyring is the one file that cannot be regenerated. Lose it and
you lose the paired identity — the Pi becomes an untrusted peer again
and every authoriser on the mesh has to re-pair it. Back up
`/var/lib/polly/keyring.json` to encrypted offline storage. The
document bytes under `/var/lib/polly/docs` are redundant across every
paired peer, so the mesh itself is your backup for content.

## What this guide deliberately doesn't cover

Any app-specific behaviour you want the Pi to run — archival crons,
status displays, background exports — is your code. The Pi peer
gives you a long-running `client.repo` with every document already
synced; compose the rest on top.

TLS for the signalling connection is handled by Cloudflare's Worker or
whatever reverse proxy fronts your Elysia app. The Pi connects over
`wss://` and verifies the cert chain through Node's default trust
store; no extra configuration needed.

## Follow-ups worth knowing

A Pi on a residential network only works when its peers can reach the
signalling server. If you want *no* third-party dependency, run the
signalling server on the Pi too (Elysia's `signalingServer` plugin,
bound to the LAN IP) and teach every peer to dial a `.local`
hostname. That stays inside the `actions-driven-app` + `mesh` surface
and does not need Cloudflare at all.

Multiple Pis on the same mesh is fine. Each pairs independently; they
will gossip document state among themselves and with browser peers.
Treat them as a resilient ring, not a primary-replica setup.
