import type { Signal } from "@preact/signals-core";

/**
 * Route pattern matching configuration
 * Examples: 'POST /todos', 'GET /todos/:id', '/todos/*'
 */
export type RoutePattern = `${string} ${string}` | string;

/**
 * State configuration for client and server
 */
export interface PollyStateConfig {
  client?: Record<string, Signal<unknown>>;
  server?: Record<string, Signal<unknown>>;
}

/**
 * Effect handler context
 */
export interface EffectContext<TResult = unknown, TBody = unknown> {
  result: TResult;
  body: TBody;
  state: {
    client: Record<string, Signal<unknown>>;
    server: Record<string, Signal<unknown>>;
  };
  params: Record<string, string>;
  clock: { tick: number; contextId: string };
}

/**
 * Client effect configuration for a route
 */
export interface ClientEffectConfig {
  /**
   * Client-side effect to run after successful response
   */
  client: (ctx: EffectContext) => void | Promise<void>;

  /**
   * Whether to broadcast this update to all connected clients
   */
  broadcast?: boolean;

  /**
   * Broadcast filter - only send to clients matching this condition
   */
  broadcastFilter?: (clientState: Record<string, Signal<unknown>>) => boolean;
}

/**
 * Authorization handler context
 */
export interface AuthorizationContext {
  state: {
    client: Record<string, Signal<unknown>>;
    server: Record<string, Signal<unknown>>;
  };
  body?: unknown;
  params?: Record<string, string>;
  headers: Record<string, string>;
}

/**
 * Authorization handler - return true to allow, false to deny
 */
export type AuthorizationHandler = (ctx: AuthorizationContext) => boolean | Promise<boolean>;

/**
 * Offline behavior configuration for a route
 */
export interface OfflineConfig<TBody = unknown, TResult = unknown> {
  /**
   * Whether to queue this request when offline
   */
  queue: boolean;

  /**
   * Optimistic update - what to show the user immediately
   */
  optimistic?: (body: TBody) => TResult;

  /**
   * Merge strategy when online again
   * - 'replace': Replace optimistic with server result
   * - 'merge': Custom merge function
   */
  merge?: "replace" | ((optimistic: TResult, server: TResult) => TResult);

  /**
   * Conflict resolution if multiple devices edited offline
   */
  conflictResolution?:
    | "last-write-wins"
    | "server-wins"
    | ((client: TResult, server: TResult) => TResult);
}

/**
 * Complete Polly middleware configuration
 */
export interface PollyConfig {
  /**
   * State signals (client and server)
   */
  state?: PollyStateConfig;

  /**
   * Client effects mapped to route patterns
   */
  effects?: Record<RoutePattern, ClientEffectConfig>;

  /**
   * Authorization rules mapped to route patterns
   */
  authorization?: Record<RoutePattern, AuthorizationHandler>;

  /**
   * Offline behavior mapped to route patterns
   */
  offline?: Record<RoutePattern, OfflineConfig>;

  /**
   * WebSocket path for real-time updates (default: '/polly/ws')
   */
  websocketPath?: string;

  /**
   * Enable TLA+ generation (default: false)
   */
  tlaGeneration?: boolean;
}

/**
 * Metadata added to responses for client wrapper
 */
export interface PollyResponseMetadata {
  /**
   * Client effect to execute
   */
  clientEffect?: {
    handler: string; // Serialized function
    broadcast: boolean;
  };

  /**
   * Offline configuration for this route
   */
  offline?: OfflineConfig;

  /**
   * Lamport clock info
   */
  clock: {
    tick: number;
    contextId: string;
  };
}
