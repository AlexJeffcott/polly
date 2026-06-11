/**
 * revocation-summary — RFC-043 wire format for the revocation-set
 * summary exchanged on every new peer connection.
 *
 * On a fresh data channel both peers send the other a summary of
 * every revocation they currently hold. After exchange each side
 * computes which entries in its own set are missing from the
 * remote's summary, and pushes those entries as full encoded
 * revocation blobs (tag 0x01). The summary itself is informative,
 * not authoritative — only the signed blob can mutate a keyring.
 *
 * Wire format: UTF-8 JSON. A summary is a sorted JSON array of
 * entries, each carrying the fields needed to detect set-difference
 * without leaking the blob's signature. Sorting is canonical so two
 * peers comparing summaries agree on order even when their stores
 * were populated in different sequences.
 *
 *   [
 *     { "r": "<revokedPeerId>", "i": "<issuerPeerId>", "t": <issuedAt> },
 *     ...
 *   ]
 *
 * Short field names keep the wire compact for keyrings with many
 * revocations. Long-form parsing isn't a goal — the format is
 * internal to the mesh protocol.
 */

/** A single entry in a revocation-set summary. */
export interface RevocationSummaryEntry {
  /** Peer id the revocation targets. */
  revokedPeerId: string;
  /** Peer id that issued the revocation. */
  issuerPeerId: string;
  /** Unix milliseconds at issue time, from the underlying RevocationRecord. */
  issuedAt: number;
}

/**
 * Encode a list of revocation entries to the canonical wire
 * representation. Entries are sorted by `revokedPeerId` then
 * `issuerPeerId` then `issuedAt` to make the comparison
 * order-independent.
 */
export function encodeRevocationSummary(
  entries: ReadonlyArray<RevocationSummaryEntry>
): Uint8Array {
  const sorted = [...entries].sort(compareSummaryEntries);
  const json = JSON.stringify(
    sorted.map((entry) => ({
      r: entry.revokedPeerId,
      i: entry.issuerPeerId,
      t: entry.issuedAt,
    }))
  );
  return new TextEncoder().encode(json);
}

/**
 * Inverse of {@link encodeRevocationSummary}. Throws on malformed
 * input — the caller is expected to drop the summary and emit a
 * diagnostic when this happens, not retry.
 */
export function decodeRevocationSummary(bytes: Uint8Array): RevocationSummaryEntry[] {
  const text = new TextDecoder().decode(bytes);
  let raw: unknown;
  try {
    raw = JSON.parse(text);
  } catch (err) {
    throw new Error(
      `decodeRevocationSummary: invalid JSON: ${err instanceof Error ? err.message : String(err)}`
    );
  }
  if (!Array.isArray(raw)) {
    throw new Error("decodeRevocationSummary: expected an array");
  }
  return raw.map((item, index): RevocationSummaryEntry => {
    if (!item || typeof item !== "object") {
      throw new Error(`decodeRevocationSummary: entry ${index} is not an object`);
    }
    const r = "r" in item ? item.r : undefined;
    const i = "i" in item ? item.i : undefined;
    const t = "t" in item ? item.t : undefined;
    if (typeof r !== "string" || typeof i !== "string" || typeof t !== "number") {
      throw new Error(`decodeRevocationSummary: entry ${index} has missing or wrong-typed fields`);
    }
    return { revokedPeerId: r, issuerPeerId: i, issuedAt: t };
  });
}

function compareSummaryEntries(a: RevocationSummaryEntry, b: RevocationSummaryEntry): number {
  if (a.revokedPeerId !== b.revokedPeerId) {
    return a.revokedPeerId < b.revokedPeerId ? -1 : 1;
  }
  if (a.issuerPeerId !== b.issuerPeerId) {
    return a.issuerPeerId < b.issuerPeerId ? -1 : 1;
  }
  return a.issuedAt - b.issuedAt;
}

/**
 * Stable key for a summary entry. Two entries with the same key
 * represent the same logical revocation. Used by the
 * peer-candidate gossip path to compute set differences.
 */
export function summaryEntryKey(entry: RevocationSummaryEntry): string {
  return `${entry.revokedPeerId}::${entry.issuerPeerId}::${entry.issuedAt}`;
}
