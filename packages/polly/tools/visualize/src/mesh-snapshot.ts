// polly#127: load and validate a captured MeshClientPeerStateSnapshot
// for the visualiser's runtime sync-state overlay.

import * as fs from "node:fs";
import type {
  MeshClientHandleSnapshot,
  MeshClientPeerStateSnapshot,
} from "../../../src/shared/lib/mesh-client";

/** The fields of a {@link MeshClientHandleSnapshot} the overlay reads. */
export type OverlayHandleSnapshot = Pick<MeshClientHandleSnapshot, "docSynchronizerExists"> &
  Partial<Pick<MeshClientHandleSnapshot, "docSynchronizerKnowsPeer" | "peerDocumentStatus">>;

/** The fields of one snapshot peer the overlay reads; `slot` absent means no negotiated slot. */
export interface OverlayPeerSnapshot {
  peerId: string;
  slot?: { handles: Record<string, OverlayHandleSnapshot> };
}

/**
 * The part of a {@link MeshClientPeerStateSnapshot} the overlay reads. A full
 * captured snapshot is assignable to it; a hand-authored one need only carry
 * these fields.
 */
export interface OverlaySnapshot
  extends Pick<MeshClientPeerStateSnapshot, "localPeerId" | "knownPeerIds" | "presentPeerIds"> {
  peers: OverlayPeerSnapshot[];
}

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

/** Validate one per-document handle entry and keep the fields the overlay
 * reads; everything else is dropped. */
function validateHandle(value: unknown, path: string): OverlayHandleSnapshot {
  if (!isObject(value)) {
    throw new MeshSnapshotError(`${path} must be an object`);
  }
  const exists = value["docSynchronizerExists"];
  if (typeof exists !== "boolean") {
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
  return {
    docSynchronizerExists: exists,
    docSynchronizerKnowsPeer: knowsPeer,
    peerDocumentStatus: status,
  };
}

function validatePeer(value: unknown, path: string): OverlayPeerSnapshot {
  if (!isObject(value)) {
    throw new MeshSnapshotError(`${path} must be an object`);
  }
  const peerId = value["peerId"];
  if (typeof peerId !== "string") {
    throw new MeshSnapshotError(`${path}.peerId must be a string`);
  }
  // A peer with no negotiated slot serialises as an omitted key; a
  // hand-authored snapshot may use an explicit null. Both mean "absent".
  const slot = value["slot"];
  if (slot === undefined || slot === null) {
    return { peerId };
  }
  if (!isObject(slot)) {
    throw new MeshSnapshotError(`${path}.slot must be an object or absent`);
  }
  const handles = slot["handles"];
  if (!isObject(handles)) {
    throw new MeshSnapshotError(`${path}.slot.handles must be an object`);
  }
  const validated: Record<string, OverlayHandleSnapshot> = {};
  for (const [docId, handle] of Object.entries(handles)) {
    validated[docId] = validateHandle(handle, `${path}.slot.handles[${docId}]`);
  }
  return { peerId, slot: { handles: validated } };
}

/** Validate a parsed JSON value against the snapshot contract and keep the
 * fields the overlay reads. */
export function validateMeshSnapshot(data: unknown): OverlaySnapshot {
  if (!isObject(data)) {
    throw new MeshSnapshotError("snapshot must be a JSON object");
  }
  const localPeerId = data["localPeerId"];
  if (typeof localPeerId !== "string") {
    throw new MeshSnapshotError("snapshot.localPeerId must be a string");
  }
  const knownPeerIds = requireStringArray(data["knownPeerIds"], "snapshot.knownPeerIds");
  const presentPeerIds = requireStringArray(data["presentPeerIds"], "snapshot.presentPeerIds");
  const peers: unknown = data["peers"];
  if (!Array.isArray(peers)) {
    throw new MeshSnapshotError("snapshot.peers must be an array");
  }
  return {
    localPeerId,
    knownPeerIds,
    presentPeerIds,
    peers: peers.map((peer: unknown, i) => validatePeer(peer, `snapshot.peers[${i}]`)),
  };
}

/** Read, parse, and validate a `MeshClientPeerStateSnapshot` JSON file.
 * Throws {@link MeshSnapshotError} with a clear message on any failure. */
export function loadMeshSnapshot(filePath: string): OverlaySnapshot {
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
export function collectSnapshotPeerIds(snapshot: OverlaySnapshot): string[] {
  const ids = new Set<string>([snapshot.localPeerId]);
  for (const id of snapshot.knownPeerIds) ids.add(id);
  for (const id of snapshot.presentPeerIds) ids.add(id);
  for (const peer of snapshot.peers) ids.add(peer.peerId);
  return [...ids];
}
