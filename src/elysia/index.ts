/**
 * Polly Elysia Middleware
 *
 * Adds distributed systems semantics to Elysia apps:
 * - State management (client + server)
 * - Authorization
 * - Offline behavior
 * - WebSocket broadcast for real-time updates
 * - TLA+ generation for verification
 *
 * Example:
 * ```typescript
 * import { Elysia } from 'elysia';
 * import { polly } from '@fairfox/polly/elysia';
 * import { $syncedState, $serverState } from '@fairfox/polly';
 *
 * const app = new Elysia()
 *   .use(polly({
 *     state: {
 *       client: {
 *         todos: $syncedState('todos', []),
 *       },
 *       server: {
 *         db: $serverState('db', db),
 *       },
 *     },
 *     effects: {
 *       'POST /todos': {
 *         client: ({ result, state }) => {
 *           state.client.todos.value = [...state.client.todos.value, result];
 *         },
 *         broadcast: true,
 *       },
 *     },
 *     authorization: {
 *       'POST /todos': ({ state }) => state.client.user.value !== null,
 *     },
 *   }))
 *   .post('/todos', handler, { body: t.Object({ text: t.String() }) });
 * ```
 */

export { polly } from "./plugin";
export type {
  AuthorizationContext,
  AuthorizationHandler,
  ClientEffectConfig,
  EffectContext,
  OfflineConfig,
  PollyConfig,
  PollyResponseMetadata,
  PollyStateConfig,
  RoutePattern,
} from "./types";
