/**
 * `sweepSealed` — storage-adapter garbage collection of sealed mesh-doc
 * bytes (polly#121).
 *
 * When a consumer compacts a `$meshState` document it seeds a fresh
 * successor and leaves an in-band sentinel in the old document. polly's
 * {@link RedirectDetector} follows that sentinel so live wrappers rebind
 * transparently — but the old document's bytes then sit in storage
 * forever, because nothing removes them.
 *
 * `sweepSealed` is that missing GC step. polly owns the walk, the
 * open-handle gate, the age window, the dry-run report and the byte
 * removal. The consumer owns the sentinel shape — it is the very
 * document the consumer's {@link RedirectDetector} already inspects —
 * supplied here as the {@link SweepSealedOptions.isSealed} predicate.
 * polly deliberately does not define a canonical sentinel format: that
 * would compete with the one consumers' detectors already read.
 *
 * polly never runs this on a timer. The consumer calls it explicitly.
 *
 * ## Redirect-index-not-yet-synced hazard
 *
 * A peer whose redirect index (`mesh:document-index`) has not yet synced
 * may still reach for a sealed document by its *old* docId. If the sweep
 * has just removed that document's bytes, the peer gets a
 * missing-document error instead of a redirect. Two gates bound the risk,
 * and the caller must size them deliberately:
 *
 *  - `olderThan` — only documents sealed longer ago than this window are
 *    swept. Make it comfortably larger than the worst-case time a peer
 *    can stay offline-then-resync, so any peer that could still hold the
 *    old docId has had the redirect delivered.
 *  - the open-handle gate — a document with a live handle on the supplied
 *    `repo` is never swept, regardless of age.
 *
 * Neither gate can see a peer that is currently offline; `olderThan` is
 * the only protection there. Choose it conservatively.
 */

import type {
  Chunk,
  DocumentId,
  Repo,
  StorageAdapterInterface,
} from "@automerge/automerge-repo/slim";
import { Automerge } from "@automerge/automerge-repo/slim";

export interface SweepSealedOptions {
  /** The Repo whose storage is swept. Its open handles gate removal. */
  repo: Repo;
  /** The storage adapter backing {@link repo}. */
  storage: StorageAdapterInterface;
  /**
   * Predicate that recognises a sealed document. Given a materialised
   * document, returns the epoch-ms timestamp at which it was sealed, or
   * `undefined` if the document is not sealed.
   *
   * This is the same document the consumer's {@link RedirectDetector}
   * inspects: the consumer owns the sentinel shape, polly never defines
   * it. The returned timestamp feeds both the {@link olderThan} filter
   * and the dry-run report.
   */
  isSealed: (doc: unknown) => number | undefined;
  /** Sweep only documents sealed more than this many milliseconds ago. */
  olderThan: number;
  /**
   * The candidate documents to consider. When omitted, the sweep
   * enumerates the whole adapter via `storage.loadRange([])`.
   *
   * That whole-adapter enumeration works for the IndexedDB and
   * in-memory adapters but **not** the NodeFS adapter, whose `loadRange`
   * requires at least a documentId prefix. Server-side callers should
   * use {@link PeerRepoServer.sweepSealed}, which enumerates the
   * filesystem and supplies this list; per-document `loadRange` then
   * works on every adapter.
   */
  documentIds?: Iterable<string>;
  /** When true, report candidates without removing anything. */
  dryRun?: boolean;
  /** Clock source, injectable for tests. Defaults to {@link Date.now}. */
  now?: () => number;
}

/** A document removed by the sweep — or, under `dryRun`, that would be. */
export interface SweptDoc {
  documentId: DocumentId;
  /** Epoch-ms the document was sealed, as reported by `isSealed`. */
  sealedAt: number;
  /** Total bytes across the document's storage chunks. */
  byteSize: number;
}

/** Why a sealed document was left in place rather than swept. */
export type KeptReason = "open-handle" | "too-recent";

/** A sealed document the sweep deliberately did not remove. */
export interface KeptDoc {
  documentId: DocumentId;
  reason: KeptReason;
}

export interface SweepResult {
  /** Documents removed — or, under `dryRun`, that would be removed. */
  swept: SweptDoc[];
  /** Sealed documents deliberately left in place, with the reason. */
  kept: KeptDoc[];
  /** Echoes the `dryRun` flag the sweep ran under. */
  dryRun: boolean;
}

/** Concatenate chunk payloads into one buffer for a single load call. */
function concat(parts: Uint8Array[]): Uint8Array {
  let total = 0;
  for (const part of parts) total += part.byteLength;
  const out = new Uint8Array(total);
  let offset = 0;
  for (const part of parts) {
    out.set(part, offset);
    offset += part.byteLength;
  }
  return out;
}

/**
 * Materialise a document from its storage chunks. Snapshot chunks are
 * loaded before incrementals so the loader has its base first;
 * `sync-state` chunks are not document data and are excluded. A document
 * whose bytes fail to load (corrupt or partial) yields `undefined` and
 * is left untouched by the sweep.
 */
function materialise(chunks: Chunk[]): unknown | undefined {
  const content = chunks
    .filter(
      (chunk): chunk is Chunk & { data: Uint8Array } =>
        chunk.key[1] !== "sync-state" && chunk.data !== undefined
    )
    .sort((a, b) => (a.key[1] === "snapshot" ? 0 : 1) - (b.key[1] === "snapshot" ? 0 : 1));
  if (content.length === 0) return undefined;
  try {
    return Automerge.loadIncremental(Automerge.init(), concat(content.map((chunk) => chunk.data)));
  } catch {
    return undefined;
  }
}

/**
 * Load the storage chunks for every candidate document and group the
 * flat chunk stream back into documents keyed by documentId.
 *
 * Each storage key is `[documentId, chunkType, chunkId]`. With an
 * explicit `documentIds` list each document is loaded by its own prefix
 * (supported by every adapter); without one, a whole-adapter
 * `loadRange([])` is used (supported by IndexedDB and in-memory adapters,
 * but not NodeFS — see {@link SweepSealedOptions.documentIds}).
 */
async function collectChunksByDocument(
  storage: StorageAdapterInterface,
  documentIds: Iterable<string> | undefined
): Promise<Map<string, Chunk[]>> {
  const chunks: Chunk[] = [];
  if (documentIds === undefined) {
    chunks.push(...(await storage.loadRange([])));
  } else {
    for (const documentId of documentIds) {
      chunks.push(...(await storage.loadRange([documentId])));
    }
  }

  const byDocument = new Map<string, Chunk[]>();
  for (const chunk of chunks) {
    const documentId = chunk.key[0];
    if (documentId === undefined) continue;
    const existing = byDocument.get(documentId);
    if (existing) existing.push(chunk);
    else byDocument.set(documentId, [chunk]);
  }
  return byDocument;
}

/** The sweep's decision for one document. */
type Verdict =
  | { action: "sweep"; entry: SweptDoc }
  | { action: "keep"; entry: KeptDoc }
  | { action: "ignore" };

/**
 * Decide what to do with one document: ignore it if it does not load or
 * is not sealed; keep it if it has an open handle or was sealed too
 * recently; otherwise mark it for sweeping.
 */
function classifyDocument(
  documentId: string,
  chunks: Chunk[],
  context: {
    repo: Repo;
    isSealed: (doc: unknown) => number | undefined;
    olderThan: number;
    at: number;
  }
): Verdict {
  const doc = materialise(chunks);
  if (doc === undefined) return { action: "ignore" };

  const sealedAt = context.isSealed(doc);
  if (sealedAt === undefined) return { action: "ignore" }; // not sealed — never swept

  // Storage keys carry raw document-id strings; brand for Repo lookups.
  const id = documentId as unknown as DocumentId;

  // Open-handle gate: a document with a live handle on this Repo is
  // never swept, regardless of age.
  if (context.repo.handles[id] !== undefined) {
    return { action: "keep", entry: { documentId: id, reason: "open-handle" } };
  }

  // Age gate: only documents sealed longer ago than the window.
  if (context.at - sealedAt < context.olderThan) {
    return { action: "keep", entry: { documentId: id, reason: "too-recent" } };
  }

  const byteSize = chunks.reduce((sum, chunk) => sum + (chunk.data?.byteLength ?? 0), 0);
  return { action: "sweep", entry: { documentId: id, sealedAt, byteSize } };
}

/**
 * Garbage-collect sealed mesh-doc bytes from a Repo's storage adapter.
 *
 * Walks every candidate document, materialises it, and asks
 * {@link SweepSealedOptions.isSealed} whether it is sealed. A sealed
 * document is removed only when it has no open handle on the Repo *and*
 * was sealed longer ago than `olderThan`; otherwise it is reported under
 * `kept` with the reason. Unsealed documents are never touched and never
 * reported. With `dryRun`, candidates are reported but nothing is removed.
 *
 * See the module doc comment for the redirect-index-not-yet-synced
 * hazard that `olderThan` and the open-handle gate exist to bound.
 */
export async function sweepSealed(options: SweepSealedOptions): Promise<SweepResult> {
  const { repo, storage, isSealed, olderThan } = options;
  const dryRun = options.dryRun ?? false;
  const now = options.now ?? Date.now;

  const byDocument = await collectChunksByDocument(storage, options.documentIds);

  const swept: SweptDoc[] = [];
  const kept: KeptDoc[] = [];
  const at = now();

  for (const [documentId, chunks] of byDocument) {
    const verdict = classifyDocument(documentId, chunks, { repo, isSealed, olderThan, at });
    if (verdict.action === "keep") {
      kept.push(verdict.entry);
    } else if (verdict.action === "sweep") {
      swept.push(verdict.entry);
      if (!dryRun) await storage.removeRange([documentId]);
    }
  }

  return { swept, kept, dryRun };
}
