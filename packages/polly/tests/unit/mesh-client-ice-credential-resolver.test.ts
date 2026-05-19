/**
 * Unit tests for the iceCredentialResolver hook on createMeshClient.
 *
 * The hook lets consumers fetch short-lived TURN credentials from their
 * own backend at connect time. Without TURN, two peers behind symmetric
 * NATs (cellular CGNAT, some corporate firewalls) cannot exchange bytes
 * even when polly's signalling layer puts them in touch — so the
 * resolver is the single integration point a production deployment
 * needs.
 *
 * These tests target {@link resolveIceServers} — the small helper
 * extracted from createMeshClient so the wiring can be verified without
 * a real WebSocket. End-to-end traversal coverage (a docker-compose
 * fixture with distinct NAT kinds) is a separate future investment;
 * this layer proves the hook reaches the adapter.
 */

import { describe, expect, test } from "bun:test";
import { resolveIceServers } from "@/shared/lib/mesh-client";

describe("resolveIceServers", () => {
  test("returns undefined when no rtc options are set", async () => {
    const result = await resolveIceServers(undefined);
    expect(result).toBeUndefined();
  });

  test("returns undefined when neither iceServers nor resolver is set", async () => {
    const result = await resolveIceServers({});
    expect(result).toBeUndefined();
  });

  test("returns the static iceServers list when no resolver is set", async () => {
    const iceServers: RTCIceServer[] = [{ urls: "stun:stun.l.google.com:19302" }];
    const result = await resolveIceServers({ iceServers });
    expect(result).toEqual(iceServers);
  });

  test("calls the resolver and returns its output when set", async () => {
    const turnServers: RTCIceServer[] = [
      {
        urls: "turn:turn.example.com",
        username: "ephemeral-user",
        credential: "ephemeral-pass",
      },
    ];
    const result = await resolveIceServers({
      iceCredentialResolver: async () => turnServers,
    });
    expect(result).toEqual(turnServers);
  });

  test("resolver wins when both iceServers and resolver are set", async () => {
    const staticServers: RTCIceServer[] = [{ urls: "stun:stun.l.google.com:19302" }];
    const resolverServers: RTCIceServer[] = [
      { urls: "turn:turn.example.com", username: "u", credential: "p" },
    ];
    const result = await resolveIceServers({
      iceServers: staticServers,
      iceCredentialResolver: async () => resolverServers,
    });
    expect(result).toEqual(resolverServers);
  });

  test("calls the resolver exactly once per resolution", async () => {
    let calls = 0;
    const resolver = async (): Promise<RTCIceServer[]> => {
      calls += 1;
      return [{ urls: "turn:turn.example.com" }];
    };
    await resolveIceServers({ iceCredentialResolver: resolver });
    expect(calls).toBe(1);
  });

  test("propagates a rejection from the resolver", async () => {
    const failure = new Error("backend unreachable");
    const resolver = async (): Promise<RTCIceServer[]> => {
      throw failure;
    };
    await expect(resolveIceServers({ iceCredentialResolver: resolver })).rejects.toBe(failure);
  });

  test("supports a synchronous resolver shape (returns a Promise)", async () => {
    // The signature is async, but TypeScript permits a synchronous
    // implementation because Promise<T> contains T. Verify the helper
    // does not assume await-able behaviour beyond the contract.
    const resolver = (): Promise<RTCIceServer[]> =>
      Promise.resolve([{ urls: "turn:turn.example.com" }]);
    const result = await resolveIceServers({ iceCredentialResolver: resolver });
    expect(result).toEqual([{ urls: "turn:turn.example.com" }]);
  });
});
