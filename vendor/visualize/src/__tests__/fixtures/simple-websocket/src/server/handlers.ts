// Message handlers with type guards

import type { RequestMessage, QueryMessage, CommandMessage, AuthMessage } from './types';
import { userService, authService } from './service';

/**
 * Type guard for query messages
 */
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query';
}

/**
 * Type guard for command messages
 */
export function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === 'command';
}

/**
 * Type guard for auth messages
 */
export function isAuthMessage(msg: RequestMessage): msg is AuthMessage {
  return msg.type === 'auth';
}

/**
 * Handle query message
 */
export async function handleQuery(message: QueryMessage): Promise<string> {
  const result = await userService.listUsers();
  return JSON.stringify({ type: 'query-result', data: result });
}

/**
 * Handle command message
 */
export async function handleCommand(message: CommandMessage): Promise<string> {
  const success = await userService.executeUserCommand(message.action, message.payload);
  return JSON.stringify({ type: 'command-result', success });
}

/**
 * Handle auth message
 */
export async function handleAuth(message: AuthMessage): Promise<string> {
  const authenticated = await authService.authenticate(message.token);
  return JSON.stringify({ type: 'auth-result', authenticated });
}

/**
 * Route message to appropriate handler
 */
export async function routeMessage(message: RequestMessage): Promise<string> {
  if (isQueryMessage(message)) {
    return await handleQuery(message);
  } else if (isCommandMessage(message)) {
    return await handleCommand(message);
  } else if (isAuthMessage(message)) {
    return await handleAuth(message);
  }

  return JSON.stringify({ type: 'error', message: 'Unknown message type' });
}
