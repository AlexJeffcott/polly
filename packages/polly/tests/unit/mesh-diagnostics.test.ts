import { afterEach, describe, expect, test } from "bun:test";
import {
  clearMeshDiagnosticListeners,
  emitMeshDiagnostic,
  recordMeshDiagnostics,
  subscribeToMeshDiagnostics,
} from "../../src/shared/lib/mesh-diagnostics";

describe("mesh-diagnostics", () => {
  afterEach(() => {
    clearMeshDiagnosticListeners();
  });

  test("subscribe delivers emitted events to the listener", () => {
    const seen: string[] = [];
    subscribeToMeshDiagnostics((event) => {
      seen.push(event.kind);
    });

    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "peer-a" });
    emitMeshDiagnostic({ kind: "drop:revoked-peer", senderId: "peer-b" });

    expect(seen).toEqual(["drop:unknown-peer", "drop:revoked-peer"]);
  });

  test("unsubscribe returned by subscribe stops further deliveries", () => {
    const seen: string[] = [];
    const stop = subscribeToMeshDiagnostics((event) => {
      seen.push(event.kind);
    });

    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "peer-a" });
    stop();
    emitMeshDiagnostic({ kind: "drop:revoked-peer", senderId: "peer-b" });

    expect(seen).toEqual(["drop:unknown-peer"]);
  });

  test("emit stamps a timestamp on every event", () => {
    const captured: number[] = [];
    subscribeToMeshDiagnostics((event) => {
      captured.push(event.timestamp);
    });

    const before = Date.now();
    emitMeshDiagnostic({ kind: "pair:invite-issued", peerId: "peer-c" });
    const after = Date.now();

    expect(captured).toHaveLength(1);
    const ts = captured[0] as number;
    expect(ts).toBeGreaterThanOrEqual(before);
    expect(ts).toBeLessThanOrEqual(after);
  });

  test("a listener exception does not block other listeners", () => {
    const seen: string[] = [];
    subscribeToMeshDiagnostics(() => {
      throw new Error("boom");
    });
    subscribeToMeshDiagnostics((event) => {
      seen.push(event.kind);
    });

    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "peer-d" });

    expect(seen).toEqual(["drop:unknown-peer"]);
  });

  test("subscribing the same listener reference twice registers it once", () => {
    let count = 0;
    const listener = () => {
      count += 1;
    };
    subscribeToMeshDiagnostics(listener);
    subscribeToMeshDiagnostics(listener);

    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "peer-e" });

    expect(count).toBe(1);
  });

  test("recordMeshDiagnostics captures every event into a shared buffer", () => {
    const { events, stop } = recordMeshDiagnostics();

    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "peer-f" });
    emitMeshDiagnostic({
      kind: "drop:bad-signature",
      senderId: "peer-g",
      reason: "signature verification failed",
    });

    expect(events).toHaveLength(2);
    expect(events[0]?.kind).toBe("drop:unknown-peer");
    expect(events[1]?.kind).toBe("drop:bad-signature");

    stop();
    emitMeshDiagnostic({ kind: "drop:revoked-peer", senderId: "peer-h" });
    expect(events).toHaveLength(2);
  });

  test("clearMeshDiagnosticListeners drops every subscriber", () => {
    const seen: string[] = [];
    subscribeToMeshDiagnostics((event) => {
      seen.push(event.kind);
    });
    subscribeToMeshDiagnostics((event) => {
      seen.push(event.kind);
    });
    clearMeshDiagnosticListeners();

    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "peer-i" });

    expect(seen).toEqual([]);
  });

  test("all silent-drop diagnostic kinds carry the senderId or document context", () => {
    const captured: ReturnType<typeof recordMeshDiagnostics>["events"] = (() => {
      const r = recordMeshDiagnostics();
      emitMeshDiagnostic({
        kind: "drop:malformed-signed-envelope",
        reason: "truncated",
      });
      emitMeshDiagnostic({
        kind: "drop:revoked-peer",
        senderId: "rev",
      });
      emitMeshDiagnostic({
        kind: "drop:unknown-peer",
        senderId: "unk",
      });
      emitMeshDiagnostic({
        kind: "drop:bad-signature",
        senderId: "sig",
        reason: "bad sig",
      });
      emitMeshDiagnostic({
        kind: "drop:malformed-encrypted-envelope",
        senderId: "enc",
        reason: "truncated",
      });
      emitMeshDiagnostic({
        kind: "drop:missing-doc-key",
        senderId: "key",
        documentId: "doc-1",
      });
      emitMeshDiagnostic({
        kind: "drop:bad-decryption",
        senderId: "dec",
        documentId: "doc-2",
        reason: "auth tag mismatch",
      });
      return r.events;
    })();

    expect(captured.map((e) => e.kind)).toEqual([
      "drop:malformed-signed-envelope",
      "drop:revoked-peer",
      "drop:unknown-peer",
      "drop:bad-signature",
      "drop:malformed-encrypted-envelope",
      "drop:missing-doc-key",
      "drop:bad-decryption",
    ]);
  });
});
