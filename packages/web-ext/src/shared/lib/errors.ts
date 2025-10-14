// Custom error classes for the extension

import type { LoggerAdapter } from "../adapters/logger.adapter";

/**
 * Base error class for all extension errors
 */
export class ExtensionError extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly context?: Record<string, unknown>
  ) {
    super(message);
    this.name = this.constructor.name;
    Error.captureStackTrace?.(this, this.constructor);
  }
}

/**
 * Error thrown when a message times out
 */
export class TimeoutError extends ExtensionError {
  constructor(
    message: string,
    public readonly timeoutMs: number,
    context?: Record<string, unknown>
  ) {
    super(message, "TIMEOUT_ERROR", { ...context, timeoutMs });
  }
}

/**
 * Error thrown when a connection is lost or unavailable
 */
export class ConnectionError extends ExtensionError {
  constructor(message: string, context?: Record<string, unknown>) {
    super(message, "CONNECTION_ERROR", context);
  }
}

/**
 * Error thrown by MessageRouter
 */
export class MessageRouterError extends ExtensionError {
  constructor(message: string, context?: Record<string, unknown>) {
    super(message, "MESSAGE_ROUTER_ERROR", context);
  }
}

/**
 * Error thrown when a message handler fails
 */
export class HandlerError extends ExtensionError {
  constructor(
    message: string,
    public readonly messageType: string,
    context?: Record<string, unknown>
  ) {
    super(message, "HANDLER_ERROR", { ...context, messageType });
  }
}

/**
 * Error thrown when an API request fails
 */
export class APIError extends ExtensionError {
  constructor(
    message: string,
    public readonly statusCode: number,
    context?: Record<string, unknown>
  ) {
    super(message, "API_ERROR", { ...context, statusCode });
  }
}

/**
 * Error thrown when offscreen document operations fail
 */
export class OffscreenError extends ExtensionError {
  constructor(message: string, context?: Record<string, unknown>) {
    super(message, "OFFSCREEN_ERROR", context);
  }
}

/**
 * Error utility for logging and throwing errors
 */
export class ErrorHandler {
  constructor(private logger: LoggerAdapter) {}

  /**
   * Log an error and then throw it
   */
  throw(error: ExtensionError): never {
    this.logger.error(error.message, error, error.context);
    throw error;
  }

  /**
   * Log an error and return it (for Promise.reject)
   */
  reject(error: ExtensionError): ExtensionError {
    this.logger.error(error.message, error, error.context);
    return error;
  }

  /**
   * Wrap an unknown error in an ExtensionError
   */
  wrap(
    error: unknown,
    message: string,
    code: string,
    context?: Record<string, unknown>
  ): ExtensionError {
    const originalError = error instanceof Error ? error : new Error(String(error));
    const wrappedError = new ExtensionError(`${message}: ${originalError.message}`, code, {
      ...context,
      originalError: originalError.message,
      originalStack: originalError.stack,
    });

    // Preserve original stack if available
    if (originalError.stack) {
      wrappedError.stack = originalError.stack;
    }

    this.logger.error(wrappedError.message, wrappedError, wrappedError.context);
    return wrappedError;
  }
}
