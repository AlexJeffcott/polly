/**
 * Minimal source-map lookup for the browser runner's stack reports.
 *
 * When a page wedges, the runner pauses it and prints the frames it was
 * executing. Those positions are in the served bundle, which is one long
 * generated file — "(inline):199:4" names the right line of the wrong file.
 * Resolving them through the bundle's own inline source map turns the report
 * into the position in the test or component the author wrote (polly#177).
 *
 * Only what that needs is implemented: decode `mappings`, and answer
 * "which original position covers this generated one". No names, no
 * `sourcesContent`, no index maps — Bun.build does not emit those here.
 */

const BASE64_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/** One decoded mapping segment: where a generated column comes from. */
interface Segment {
  generatedColumn: number;
  sourceIndex: number;
  sourceLine: number;
  sourceColumn: number;
}

interface SourceMap {
  sources: string[];
  mappings: string;
}

/** Resolves a generated position to `source:line:column`, or undefined. */
export type SourceMapLookup = (line: number, column: number) => string | undefined;

/** Decode one Base64 VLQ segment into its signed fields. */
function decodeSegment(segment: string): number[] {
  const fields: number[] = [];
  let shift = 0;
  let value = 0;
  for (const char of segment) {
    const digit = BASE64_ALPHABET.indexOf(char);
    if (digit === -1) return [];
    const hasContinuation = (digit & 32) !== 0;
    value += (digit & 31) << shift;
    if (hasContinuation) {
      shift += 5;
      continue;
    }
    const negative = (value & 1) === 1;
    const magnitude = value >> 1;
    fields.push(negative ? -magnitude : magnitude);
    value = 0;
    shift = 0;
  }
  return fields;
}

/** Decode the whole `mappings` string into per-generated-line segments. */
function decodeMappings(mappings: string): Segment[][] {
  const lines: Segment[][] = [];
  // The four fields are deltas carried across the entire map, not per line —
  // except the generated column, which resets on every line.
  let sourceIndex = 0;
  let sourceLine = 0;
  let sourceColumn = 0;
  for (const lineText of mappings.split(";")) {
    const segments: Segment[] = [];
    let generatedColumn = 0;
    for (const segmentText of lineText.split(",")) {
      if (!segmentText) continue;
      const fields = decodeSegment(segmentText);
      const [columnDelta, sourceDelta, lineDelta, sourceColumnDelta] = fields;
      if (columnDelta === undefined) continue;
      generatedColumn += columnDelta;
      // A one-field segment marks generated code with no origin; skip it.
      if (sourceDelta === undefined || lineDelta === undefined || sourceColumnDelta === undefined) {
        continue;
      }
      sourceIndex += sourceDelta;
      sourceLine += lineDelta;
      sourceColumn += sourceColumnDelta;
      segments.push({ generatedColumn, sourceIndex, sourceLine, sourceColumn });
    }
    lines.push(segments);
  }
  return lines;
}

/** Pull the inline source map out of a bundle, if it carries one. */
export function parseInlineSourceMap(bundle: string): SourceMap | undefined {
  const match = bundle.match(
    /\/\/# sourceMappingURL=data:application\/json;(?:charset=[^;]+;)?base64,([A-Za-z0-9+/=]+)/
  );
  const encoded = match?.[1];
  if (!encoded) return undefined;
  try {
    const parsed: unknown = JSON.parse(Buffer.from(encoded, "base64").toString("utf8"));
    if (typeof parsed !== "object" || parsed === null) return undefined;
    const { sources, mappings } = parsed as { sources?: unknown; mappings?: unknown };
    if (!Array.isArray(sources) || typeof mappings !== "string") return undefined;
    return { sources: sources.map(String), mappings };
  } catch {
    return undefined;
  }
}

/**
 * Build a lookup over a bundle's inline source map.
 *
 * `lineOffset` is how many lines of wrapper HTML sit above the bundle in the
 * served document, since the debugger reports positions in the document, not
 * in the script. Returns undefined when the bundle carries no usable map, so
 * callers can fall back to the raw generated position.
 */
export function createSourceMapLookup(bundle: string, lineOffset = 0): SourceMapLookup | undefined {
  const map = parseInlineSourceMap(bundle);
  if (!map) return undefined;
  const lines = decodeMappings(map.mappings);

  return (line: number, column: number): string | undefined => {
    const generatedLine = line - lineOffset;
    if (generatedLine < 0) return undefined;
    const segments = lines[generatedLine];
    if (!segments || segments.length === 0) return undefined;
    // The last segment starting at or before the column owns that position.
    let best = segments[0];
    for (const segment of segments) {
      if (segment.generatedColumn > column) break;
      best = segment;
    }
    if (!best) return undefined;
    const source = map.sources[best.sourceIndex] ?? "(unknown source)";
    return `${source}:${best.sourceLine + 1}:${best.sourceColumn}`;
  };
}
