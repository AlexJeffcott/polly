/**
 * @fairfox/polly/test — ephemeral listen ports.
 *
 * A test that draws a listen port at random from a fixed window can collide
 * with itself, with a second copy of the suite, or with any other process
 * holding a port in that window. The integration suite drew 27 ports from a
 * 10,000-port window, which is a 3.45% self-collision probability per run
 * (birthday bound, `1 - exp(-n(n-1)/2N)`) and a lower bound at that. A
 * collision fails `listen()` and reads as flake, so the natural response is a
 * retry — which narrows the window instead of removing it (polly#174).
 *
 * Port 0 asks the kernel for a free port. The server owns that port from the
 * moment it is assigned, so no other process can take it in between. These
 * helpers read the assigned port back off the two server shapes polly binds:
 *
 *   - Bun/Elysia — `app.server.port`, after `.listen(0)`
 *   - `ws` WebSocketServer — `wss.address().port`, after `{ port: 0 }`
 *
 * `retryOnPortInUse` covers the one case port 0 cannot: a port that must be
 * known before the server starts, such as a restart on the same port.
 */

/** Elysia hangs the underlying Bun server off `.server`. */
interface BunServerHost {
  server?: { port?: number | null } | null;
}

/** `ws`'s WebSocketServer reports its bound address as an AddressInfo. */
interface AddressHost {
  address?: () => string | { port?: number | null } | null;
}

/**
 * Read the port a Bun/Elysia app was actually assigned.
 *
 * @param app An Elysia app (or any Bun server host) already `.listen(0)`-ed.
 * @throws If the app is not listening — a caller reading the port before the
 *   listen resolves gets a named failure, not a URL containing `undefined`.
 *
 * @example
 * ```typescript
 * const app = new Elysia().use(signalingServer({ path })).listen(0);
 * const url = `ws://127.0.0.1:${resolveListenPort(app)}${path}`;
 * ```
 */
export function resolveListenPort(app: unknown): number {
  const port = (app as unknown as BunServerHost).server?.port;
  if (typeof port !== "number" || port <= 0) {
    throw new Error(
      `resolveListenPort: app is not listening (server.port = ${String(port)}). ` +
        "Call .listen(0) and read the port from the returned app."
    );
  }
  return port;
}

/**
 * Read the port a `ws` WebSocketServer was actually assigned.
 *
 * @param wss A WebSocketServer constructed with `{ port: 0 }` and already
 *   listening — `createPeerRepoServer` awaits that before it returns.
 * @throws If the server is not listening on a TCP port.
 *
 * @example
 * ```typescript
 * const server = await createPeerRepoServer({ port: 0, host: "127.0.0.1", storagePath });
 * const url = `ws://127.0.0.1:${resolveWebSocketPort(server.webSocketServer)}`;
 * ```
 */
export function resolveWebSocketPort(wss: unknown): number {
  const address = (wss as unknown as AddressHost).address?.();
  const port = typeof address === "object" && address !== null ? address.port : undefined;
  if (typeof port !== "number" || port <= 0) {
    throw new Error(
      `resolveWebSocketPort: server is not listening on a TCP port (address = ${JSON.stringify(address)}).`
    );
  }
  return port;
}

/** Bun, Node and `ws` all word an occupied-port failure differently. */
function isPortInUse(error: unknown): boolean {
  if (error instanceof Error && "code" in error && error.code === "EADDRINUSE") return true;
  const message = error instanceof Error ? error.message : String(error);
  return /EADDRINUSE|address already in use|is port \d+ in use|Failed to start server/i.test(
    message
  );
}

export interface RetryOnPortInUseOptions {
  /** How many times to call `start` in total. Defaults to 5. */
  attempts?: number;
  /** Pause between attempts, in milliseconds. Defaults to 100. */
  delayMs?: number;
}

/**
 * Start a server on a port that is already decided, retrying a bounded number
 * of times while the port is still held.
 *
 * Only for the case port 0 cannot serve: the port must be known before the
 * server starts — a restart on the same port, or a URL handed out in advance.
 * A retry narrows the collision window rather than removing it, so prefer
 * `.listen(0)` plus {@link resolveListenPort} everywhere else.
 *
 * The final failure is the bind error itself, so the test reports "port in
 * use" rather than timing out on a connection to a server that never started.
 *
 * @example
 * ```typescript
 * const app = await retryOnPortInUse(() => startSignaling(port));
 * ```
 */
export async function retryOnPortInUse<T>(
  start: () => T | Promise<T>,
  options: RetryOnPortInUseOptions = {}
): Promise<T> {
  const attempts = options.attempts ?? 5;
  const delayMs = options.delayMs ?? 100;
  let lastError: unknown;
  for (let attempt = 1; attempt <= attempts; attempt += 1) {
    try {
      return await start();
    } catch (error) {
      if (!isPortInUse(error)) throw error;
      lastError = error;
      if (attempt < attempts) await new Promise((r) => setTimeout(r, delayMs));
    }
  }
  throw lastError;
}
