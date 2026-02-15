/**
 * Lamport Clock Implementation
 *
 * Provides logical timestamps for distributed systems to establish
 * causal ordering of events across different contexts (client/server).
 *
 * Key properties:
 * - Each event increments the local clock
 * - When receiving a message, clock = max(local, received) + 1
 * - If A happens before B, then timestamp(A) < timestamp(B)
 *
 * References:
 * - Lamport, L. (1978). "Time, Clocks, and the Ordering of Events in a Distributed System"
 * - https://lamport.azurewebsites.net/pubs/time-clocks.pdf
 */

/**
 * Lamport clock state
 */
export interface LamportClock {
  tick: number;
  contextId: string;
}

/**
 * Lamport clock with operations
 */
export interface LamportClockOps {
  /**
   * Get current clock value
   */
  now(): LamportClock;

  /**
   * Increment the clock (before sending a message or performing an action)
   */
  tick(): number;

  /**
   * Update clock when receiving a message
   * Sets clock to max(local, received) + 1
   */
  update(receivedClock: LamportClock): void;
}

/**
 * Create a Lamport clock for a specific context
 *
 * @param contextId - Unique identifier for this context (e.g., "client", "server", "worker-1")
 * @returns Clock operations
 *
 * @example
 * ```typescript
 * const serverClock = createLamportClock("server");
 *
 * // Before sending a message
 * serverClock.tick();
 * const timestamp = serverClock.now();
 * send({ data: "...", clock: timestamp });
 *
 * // When receiving a message
 * onReceive((message) => {
 *   serverClock.update(message.clock);
 *   // Process message with updated clock
 * });
 * ```
 */
export function createLamportClock(contextId: string): LamportClockOps {
  let tick = 0;

  return {
    now(): LamportClock {
      return { tick, contextId };
    },

    tick(): number {
      tick += 1;
      return tick;
    },

    update(receivedClock: LamportClock): void {
      tick = Math.max(tick, receivedClock.tick) + 1;
    },
  };
}
