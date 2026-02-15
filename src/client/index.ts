/**
 * Polly Client Wrapper for Eden
 *
 * Enhances Eden treaty client with Polly features:
 * - Offline queueing
 * - WebSocket real-time updates
 * - Client effect execution (dev mode)
 * - Lamport clock synchronization
 *
 * Example:
 * ```typescript
 * import { createPollyClient } from '@fairfox/polly/client';
 * import { $syncedState } from '@fairfox/polly';
 * import type { app } from './server';
 *
 * const clientState = {
 *   todos: $syncedState('todos', []),
 * };
 *
 * export const api = createPollyClient<typeof app>('http://localhost:3000', {
 *   state: clientState,
 * });
 *
 * // Use it
 * await api.todos.post({ text: 'Buy milk' });
 *
 * // Access Polly features
 * console.log(api.$polly.state.isOnline.value); // true/false
 * console.log(api.$polly.state.queuedRequests.value); // Array of queued requests
 * ```
 */

export type { PollyClientOptions } from "./wrapper";
export { createPollyClient } from "./wrapper";
