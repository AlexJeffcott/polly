/**
 * Unit tests for the e2e-mesh test kit pieces that can be exercised
 * outside Puppeteer: withRelay (boots a real signalling server),
 * startDiagnosticRecorder (subscribes to the mesh-diagnostics stream),
 * and the console allowlist.
 */

import { afterEach, describe, expect, test } from "bun:test";
import {
  clearMeshDiagnosticListeners,
  emitMeshDiagnostic,
} from "../../src/shared/lib/mesh-diagnostics";
import {
  isAllowedConsoleLine,
  MESH_CONSOLE_ALLOWLIST,
} from "../../tools/test/src/e2e-mesh/console-allowlist";
import {
  MeshAssertionError,
  startDiagnosticRecorder,
} from "../../tools/test/src/e2e-mesh/mesh-assertions";
import { withRelay } from "../../tools/test/src/e2e-mesh/with-relay";

describe("withRelay", () => {
  test("embedded mode boots a relay on a ws:// URL and closes cleanly", async () => {
    const relay = await withRelay();
    try {
      expect(relay.url).toMatch(/^ws:\/\/127\.0\.0\.1:\d+\/polly\/signaling$/);

      // Open a WebSocket and confirm the server accepts the connection.
      const opened = await new Promise<boolean>((resolve, reject) => {
        const ws = new WebSocket(relay.url);
        const timeout = setTimeout(() => reject(new Error("did not open within 2s")), 2000);
        ws.addEventListener("open", () => {
          clearTimeout(timeout);
          ws.close();
          resolve(true);
        });
        ws.addEventListener("error", (err) => {
          clearTimeout(timeout);
          reject(err);
        });
      });
      expect(opened).toBe(true);
    } finally {
      await relay.close();
    }
  });

  test("env mode requires SIGNALING_URL", () => {
    Reflect.deleteProperty(process.env, "SIGNALING_URL");
    expect(withRelay({ mode: "env" })).rejects.toThrow(/SIGNALING_URL/);
  });

  test("env mode returns the supplied URL without booting", async () => {
    process.env["SIGNALING_URL"] = "wss://example.test/sig";
    const relay = await withRelay({ mode: "env" });
    expect(relay.url).toBe("wss://example.test/sig");
    await relay.close();
    Reflect.deleteProperty(process.env, "SIGNALING_URL");
  });

  test("custom path is honoured in the URL", async () => {
    const relay = await withRelay({ path: "/custom/sig" });
    try {
      expect(relay.url).toMatch(/\/custom\/sig$/);
    } finally {
      await relay.close();
    }
  });
});

describe("startDiagnosticRecorder", () => {
  afterEach(() => {
    clearMeshDiagnosticListeners();
  });

  test("assertNoSilentDrops passes when no diagnostics fired", () => {
    const diag = startDiagnosticRecorder();
    try {
      expect(() => diag.assertNoSilentDrops()).not.toThrow();
    } finally {
      diag.stop();
    }
  });

  test("assertNoSilentDrops fails on any unexpected drop diagnostic", () => {
    const diag = startDiagnosticRecorder();
    try {
      emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "p1" });
      expect(() => diag.assertNoSilentDrops()).toThrow(MeshAssertionError);
    } finally {
      diag.stop();
    }
  });

  test("allow list permits the named drop kinds", () => {
    const diag = startDiagnosticRecorder();
    try {
      emitMeshDiagnostic({ kind: "drop:revoked-peer", senderId: "p1" });
      emitMeshDiagnostic({ kind: "drop:revoked-peer", senderId: "p2" });
      expect(() => diag.assertNoSilentDrops(["drop:revoked-peer"])).not.toThrow();
    } finally {
      diag.stop();
    }
  });

  test("allow list does not suppress drop kinds outside the list", () => {
    const diag = startDiagnosticRecorder();
    try {
      emitMeshDiagnostic({ kind: "drop:revoked-peer", senderId: "p1" });
      emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "p2" });
      let caught: unknown;
      try {
        diag.assertNoSilentDrops(["drop:revoked-peer"]);
      } catch (err) {
        caught = err;
      }
      expect(caught).toBeInstanceOf(MeshAssertionError);
      const failure = caught as MeshAssertionError;
      expect(failure.unexpected).toHaveLength(1);
      expect(failure.unexpected[0]?.kind).toBe("drop:unknown-peer");
    } finally {
      diag.stop();
    }
  });

  test("non-drop diagnostics (pair:*, revoke:*) are ignored by assertNoSilentDrops", () => {
    const diag = startDiagnosticRecorder();
    try {
      emitMeshDiagnostic({ kind: "pair:invite-issued", peerId: "peer-a" });
      emitMeshDiagnostic({
        kind: "revoke:applied",
        revokedPeerId: "peer-b",
      });
      expect(() => diag.assertNoSilentDrops()).not.toThrow();
    } finally {
      diag.stop();
    }
  });

  test("stop() unsubscribes; later emits do not affect the buffer", () => {
    const diag = startDiagnosticRecorder();
    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "p1" });
    expect(diag.events).toHaveLength(1);
    diag.stop();
    emitMeshDiagnostic({ kind: "drop:unknown-peer", senderId: "p2" });
    expect(diag.events).toHaveLength(1);
  });
});

describe("MESH_CONSOLE_ALLOWLIST", () => {
  test("matches the polly#107 H5 warmup warning by substring", () => {
    const line = {
      level: "warn",
      text: "[polly#107 H5] $meshState resolved against unconfigured module instance abc",
    };
    expect(isAllowedConsoleLine(line)).toBe(true);
  });

  test("does not match unrelated console output", () => {
    const line = { level: "error", text: "TypeError: Cannot read property foo of undefined" };
    expect(isAllowedConsoleLine(line)).toBe(false);
  });

  test("consumer-supplied allowlist replaces the default", () => {
    const custom = [{ match: "expected-noise", reason: "test only" }];
    expect(isAllowedConsoleLine({ level: "log", text: "[polly#107 H5] warmup" }, custom)).toBe(
      false
    );
    expect(isAllowedConsoleLine({ level: "log", text: "expected-noise from app" }, custom)).toBe(
      true
    );
  });

  test("level filter restricts a pattern to a single level", () => {
    const pattern = [{ level: "error" as const, match: "boom", reason: "test only" }];
    expect(isAllowedConsoleLine({ level: "log", text: "boom" }, pattern)).toBe(false);
    expect(isAllowedConsoleLine({ level: "error", text: "boom" }, pattern)).toBe(true);
  });

  test("default allowlist exposes at least one entry", () => {
    expect(MESH_CONSOLE_ALLOWLIST.length).toBeGreaterThan(0);
  });
});
