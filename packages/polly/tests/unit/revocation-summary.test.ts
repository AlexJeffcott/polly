import { describe, expect, test } from "bun:test";
import {
  decodeRevocationSummary,
  encodeRevocationSummary,
  type RevocationSummaryEntry,
  summaryEntryKey,
} from "@/shared/lib/revocation-summary";

function entry(
  revokedPeerId: string,
  issuerPeerId: string,
  issuedAt: number
): RevocationSummaryEntry {
  return { revokedPeerId, issuerPeerId, issuedAt };
}

function decodeJson(bytes: Uint8Array): Array<{ r: string; i: string; t: number }> {
  return JSON.parse(new TextDecoder().decode(bytes));
}

describe("encodeRevocationSummary", () => {
  test("emits the compact short-key wire shape", () => {
    const bytes = encodeRevocationSummary([entry("revoked-a", "issuer-x", 1700)]);
    expect(decodeJson(bytes)).toEqual([{ r: "revoked-a", i: "issuer-x", t: 1700 }]);
  });

  test("uses exactly the short field names r/i/t and no others", () => {
    const bytes = encodeRevocationSummary([entry("rp", "ip", 5)]);
    expect(Object.keys(decodeJson(bytes)[0]!)).toEqual(["r", "i", "t"]);
  });

  test("encodes an empty list as an empty array", () => {
    expect(decodeJson(encodeRevocationSummary([]))).toEqual([]);
  });

  // Scrambled three-element inputs force the comparator through both its
  // -1 and +1 branches regardless of the engine's sort pivot order, which a
  // two-element input does not guarantee.
  test("sorts by revokedPeerId first", () => {
    const bytes = encodeRevocationSummary([
      entry("c", "issuer", 1),
      entry("a", "issuer", 1),
      entry("b", "issuer", 1),
    ]);
    expect(decodeJson(bytes).map((e) => e.r)).toEqual(["a", "b", "c"]);
  });

  test("sorts by issuerPeerId when revokedPeerId ties", () => {
    const bytes = encodeRevocationSummary([
      entry("same", "issuer-c", 1),
      entry("same", "issuer-a", 1),
      entry("same", "issuer-b", 1),
    ]);
    expect(decodeJson(bytes).map((e) => e.i)).toEqual(["issuer-a", "issuer-b", "issuer-c"]);
  });

  test("sorts by issuedAt when revokedPeerId and issuerPeerId tie", () => {
    const bytes = encodeRevocationSummary([
      entry("same", "same", 30),
      entry("same", "same", 10),
      entry("same", "same", 20),
    ]);
    expect(decodeJson(bytes).map((e) => e.t)).toEqual([10, 20, 30]);
  });

  test("is order-independent: differently-ordered inputs encode identically", () => {
    const a = encodeRevocationSummary([entry("z", "m", 9), entry("a", "m", 1), entry("a", "m", 2)]);
    const b = encodeRevocationSummary([entry("a", "m", 2), entry("z", "m", 9), entry("a", "m", 1)]);
    expect(new TextDecoder().decode(a)).toBe(new TextDecoder().decode(b));
  });

  test("does not mutate the caller's array", () => {
    const input = [entry("b", "x", 1), entry("a", "x", 1)];
    encodeRevocationSummary(input);
    expect(input.map((e) => e.revokedPeerId)).toEqual(["b", "a"]);
  });
});

describe("decodeRevocationSummary", () => {
  test("round-trips through encode", () => {
    const entries = [entry("a", "issuer-1", 100), entry("b", "issuer-2", 200)];
    expect(decodeRevocationSummary(encodeRevocationSummary(entries))).toEqual(entries);
  });

  test("maps short keys back to long field names", () => {
    const bytes = new TextEncoder().encode(JSON.stringify([{ r: "rp", i: "ip", t: 7 }]));
    expect(decodeRevocationSummary(bytes)).toEqual([
      { revokedPeerId: "rp", issuerPeerId: "ip", issuedAt: 7 },
    ]);
  });

  test("decodes an empty array", () => {
    expect(decodeRevocationSummary(new TextEncoder().encode("[]"))).toEqual([]);
  });

  test("throws on malformed JSON", () => {
    const bytes = new TextEncoder().encode("{not json");
    expect(() => decodeRevocationSummary(bytes)).toThrow(/invalid JSON/);
  });

  test("throws when the top level is not an array", () => {
    const bytes = new TextEncoder().encode(JSON.stringify({ r: "x", i: "y", t: 1 }));
    expect(() => decodeRevocationSummary(bytes)).toThrow(/expected an array/);
  });

  test("throws when an entry is not an object", () => {
    const bytes = new TextEncoder().encode(JSON.stringify(["not-an-object"]));
    expect(() => decodeRevocationSummary(bytes)).toThrow(/entry 0 is not an object/);
  });

  test("throws when an entry is null", () => {
    const bytes = new TextEncoder().encode(JSON.stringify([null]));
    expect(() => decodeRevocationSummary(bytes)).toThrow(/entry 0 is not an object/);
  });

  test("throws when r is not a string", () => {
    const bytes = new TextEncoder().encode(JSON.stringify([{ r: 1, i: "y", t: 1 }]));
    expect(() => decodeRevocationSummary(bytes)).toThrow(/wrong-typed fields/);
  });

  test("throws when i is not a string", () => {
    const bytes = new TextEncoder().encode(JSON.stringify([{ r: "x", i: 2, t: 1 }]));
    expect(() => decodeRevocationSummary(bytes)).toThrow(/wrong-typed fields/);
  });

  test("throws when t is not a number", () => {
    const bytes = new TextEncoder().encode(JSON.stringify([{ r: "x", i: "y", t: "1" }]));
    expect(() => decodeRevocationSummary(bytes)).toThrow(/wrong-typed fields/);
  });

  test("reports the offending entry index in the message", () => {
    const bytes = new TextEncoder().encode(
      JSON.stringify([
        { r: "x", i: "y", t: 1 },
        { r: "x", i: "y" },
      ])
    );
    expect(() => decodeRevocationSummary(bytes)).toThrow(/entry 1 /);
  });
});

describe("summaryEntryKey", () => {
  test("joins the three fields with a double-colon separator", () => {
    expect(summaryEntryKey(entry("revoked", "issuer", 42))).toBe("revoked::issuer::42");
  });

  test("is equal for logically-identical entries", () => {
    expect(summaryEntryKey(entry("a", "b", 1))).toBe(summaryEntryKey(entry("a", "b", 1)));
  });

  test("differs when any field differs", () => {
    const base = summaryEntryKey(entry("a", "b", 1));
    expect(summaryEntryKey(entry("a", "b", 2))).not.toBe(base);
    expect(summaryEntryKey(entry("a", "c", 1))).not.toBe(base);
    expect(summaryEntryKey(entry("x", "b", 1))).not.toBe(base);
  });
});
