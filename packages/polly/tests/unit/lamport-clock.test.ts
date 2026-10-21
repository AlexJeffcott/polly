/**
 * `createLamportClock` — the logical clock the Elysia plugin stamps onto
 * every response (`X-Polly-Metadata.clock`) and the client wrapper merges on
 * receipt. The property that matters is Lamport's: if event A happens before
 * event B, then A's tick is strictly less than B's, including across a
 * send/receive between two clocks.
 */
import { describe, expect, test } from "bun:test";
import { createLamportClock } from "@/core/clock";

describe("createLamportClock", () => {
  test("starts at zero under its own context id", () => {
    expect(createLamportClock("server").now()).toEqual({ tick: 0, contextId: "server" });
  });

  test("tick advances by one and returns the new value", () => {
    const clock = createLamportClock("server");

    expect([clock.tick(), clock.tick(), clock.tick()]).toEqual([1, 2, 3]);
    expect(clock.now().tick).toBe(3);
  });

  test("now() returns a snapshot, not a live view", () => {
    const clock = createLamportClock("server");
    const before = clock.now();

    clock.tick();

    expect(before.tick).toBe(0);
  });

  describe("update(received)", () => {
    test("a received clock ahead of the local one jumps past it", () => {
      const clock = createLamportClock("client");
      clock.tick();

      clock.update({ tick: 10, contextId: "server" });

      expect(clock.now().tick).toBe(11);
    });

    test("a received clock behind the local one still advances the local clock", () => {
      const clock = createLamportClock("client");
      for (let i = 0; i < 5; i++) clock.tick();

      clock.update({ tick: 2, contextId: "server" });

      expect(clock.now().tick).toBe(6);
    });

    test("a received clock equal to the local one advances past both", () => {
      const clock = createLamportClock("client");
      clock.tick();
      clock.tick();

      clock.update({ tick: 2, contextId: "server" });

      expect(clock.now().tick).toBe(3);
    });

    test("keeps the local context id, not the sender's", () => {
      const clock = createLamportClock("client");

      clock.update({ tick: 4, contextId: "server" });

      expect(clock.now().contextId).toBe("client");
    });

    test("a later tick continues from the merged value", () => {
      const clock = createLamportClock("client");

      clock.update({ tick: 7, contextId: "server" });

      expect(clock.tick()).toBe(9);
    });
  });

  test("a send/receive round trip orders every event strictly", () => {
    const server = createLamportClock("server");
    const client = createLamportClock("client");
    const events: number[] = [];

    // client sends a request
    events.push(client.tick());
    // server receives it, handles it, and stamps the response
    server.update(client.now());
    events.push(server.now().tick);
    events.push(server.tick());
    // client receives the response
    client.update(server.now());
    events.push(client.now().tick);

    // Strictly increasing: already in ascending order, and no tick repeats.
    expect(events).toEqual(events.toSorted((a, b) => a - b));
    expect(new Set(events).size).toBe(events.length);
  });
});
