// polly#127: load and validate a captured MeshClientPeerStateSnapshot
// for the visualiser's runtime sync-state overlay.

import * as fs from "node:fs";
import type {
  MeshClientHandleSnapshot,
  MeshClientPeerStateSnapshot,
} from "../../../src/shared/lib/mesh-client";

/** Thrown when a `--snapshot` file is missing, unreadable, or does not
 * match the {@link MeshClientPeerStateSnapshot} shape. The CLI turns it
 * into a clear message and a non-zero exit with no partial DSL. */
export class MeshSnapshotError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "MeshSnapshotError";
  }
}

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function isStringArray(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((v) => typeof v === "string");
}

function requireStringArray(value: unknown, path: string): string[] {
  if (!isStringArray(value)) {
    throw new MeshSnapshotError(`${path} must be an array of strings`);
  }
  return value;
}

/** Validate one per-document handle entry. Only the fields the overlay
 * reads are checked; everything else is passed through untouched. */
function validateHandle(value: unknown, path: string): MeshClientHandleSnapshot {
  if (!isObject(value)) {
    throw new MeshSnapshotError(`${path} must be an object`);
  }
  if (typeof value["docSynchronizerExists"] !== "boolean") {
    throw new MeshSnapshotError(`${path}.docSynchronizerExists must be a boolean`);
  }
  const knowsPeer = value["docSynchronizerKnowsPeer"];
  if (knowsPeer !== undefined && typeof knowsPeer !== "boolean") {
    throw new MeshSnapshotError(`${path}.docSynchronizerKnowsPeer must be a boolean or absent`);
  }
  const status = value["peerDocumentStatus"];
  if (status !== undefined && typeof status !== "string") {
    throw new MeshSnapshotError(`${path}.peerDocumentStatus must be a string or absent`);
  }
  return value as unknown as MeshClientHandleSnapshot;
}

function validatePeer(value: unknown, path: string): MeshClientPeerStateSnapshot["peers"][number] {
  if (!isObject(value)) {
    throw new MeshSnapshotError(`${path} must be an object`);
  }
  if (typeof value["peerId"] !== "string") {
    throw new MeshSnapshotError(`${path}.peerId must be a string`);
  }
  // A peer with no negotiated slot serialises as an omitted key; a
  // hand-authored snapshot may use an explicit null. Both mean "absent".
  const slot = value["slot"];
  if (slot !== undefined && slot !== null) {
    if (!isObject(slot)) {
      throw new MeshSnapshotError(`${path}.slot must be an object or absent`);
    }
    const handles = slot["handles"];
    if (!isObject(handles)) {
      throw new MeshSnapshotError(`${path}.slot.handles must be an object`);
    }
    for (const [docId, handle] of Object.entries(handles)) {
      validateHandle(handle, `${path}.slot.handles[${docId}]`);
    }
  }
  return value as unknown as MeshClientPeerStateSnapshot["peers"][number];
}

/** Validate a parsed JSON value against the snapshot contract. */
export function validateMeshSnapshot(data: unknown): MeshClientPeerStateSnapshot {
  if (!isObject(data)) {
    throw new MeshSnapshotError("snapshot must be a JSON object");
  }
  if (typeof data["localPeerId"] !== "string") {
    throw new MeshSnapshotError("snapshot.localPeerId must be a string");
  }
  requireStringArray(data["knownPeerIds"], "snapshot.knownPeerIds");
  requireStringArray(data["presentPeerIds"], "snapshot.presentPeerIds");
  const peers = data["peers"];
  if (!Array.isArray(peers)) {
    throw new MeshSnapshotError("snapshot.peers must be an array");
  }
  peers.forEach((peer, i) => {
    validatePeer(peer, `snapshot.peers[${i}]`);
  });
  return data as unknown as MeshClientPeerStateSnapshot;
}

/** Read, parse, and validate a `MeshClientPeerStateSnapshot` JSON file.
 * Throws {@link MeshSnapshotError} with a clear message on any failure. */
export function loadMeshSnapshot(filePath: string): MeshClientPeerStateSnapshot {
  let raw: string;
  try {
    raw = fs.readFileSync(filePath, "utf-8");
  } catch (error) {
    const reason = error instanceof Error ? error.message : String(error);
    throw new MeshSnapshotError(`cannot read snapshot file '${filePath}': ${reason}`);
  }

  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch (error) {
    const reason = error instanceof Error ? error.message : String(error);
    throw new MeshSnapshotError(`snapshot file '${filePath}' is not valid JSON: ${reason}`);
  }

  return validateMeshSnapshot(parsed);
}

/** Every distinct peer id the snapshot mentions: the local peer, the
 * keyring/signalling rosters, and every entry in `peers[]`. The overlay
 * synthesises one diagram node per id. */
export function collectSnapshotPeerIds(snapshot: MeshClientPeerStateSnapshot): string[] {
  const ids = new Set<string>([snapshot.localPeerId]);
  for (const id of snapshot.knownPeerIds) ids.add(id);
  for (const id of snapshot.presentPeerIds) ids.add(id);
  for (const peer of snapshot.peers) ids.add(peer.peerId);
  return [...ids];
}
