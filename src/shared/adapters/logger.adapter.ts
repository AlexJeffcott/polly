import type { Context, LogLevel } from "../types/messages";
// Logger adapter interface (message-based centralized logging)
import type { RuntimeAdapter } from "./runtime.adapter";

export interface LoggerAdapter {
  /**
   * Debug-level logging (verbose, development info)
   */
  debug(message: string, context?: Record<string, unknown>): void;

  /**
   * Info-level logging (general information)
   */
  info(message: string, context?: Record<string, unknown>): void;

  /**
   * Warning-level logging (non-critical issues)
   */
  warn(message: string, context?: Record<string, unknown>): void;

  /**
   * Error-level logging (errors and exceptions)
   */
  error(message: string, error?: Error, context?: Record<string, unknown>): void;

  /**
   * Log with explicit level
   */
  log(level: LogLevel, message: string, context?: Record<string, unknown>): void;
}

export interface MessageLoggerOptions {
  consoleMirror?: boolean; // Also log to console (for development)
  fallbackToConsole?: boolean; // Log to console if message send fails (default: true)
}

/**
 * Message-based logger that sends LOG messages to background LogStore
 * Uses RuntimeAdapter directly to avoid circular dependency with MessageBus
 */
export class MessageLoggerAdapter implements LoggerAdapter {
  constructor(
    private runtime: RuntimeAdapter,
    private sourceContext: Context,
    private options?: MessageLoggerOptions
  ) {}

  debug(message: string, context?: Record<string, unknown>): void {
    this.sendLog("debug", message, context);
  }

  info(message: string, context?: Record<string, unknown>): void {
    this.sendLog("info", message, context);
  }

  warn(message: string, context?: Record<string, unknown>): void {
    this.sendLog("warn", message, context);
  }

  error(message: string, error?: Error, context?: Record<string, unknown>): void {
    this.sendLog("error", message, context, error);
  }

  log(level: LogLevel, message: string, context?: Record<string, unknown>): void {
    this.sendLog(level, message, context);
  }

  private sendLog(
    level: LogLevel,
    message: string,
    context?: Record<string, unknown>,
    error?: Error
  ): void {
    // Optional console mirror for development
    if (this.options?.consoleMirror) {
      const consoleMethod = console[level] || console.log;
      consoleMethod(`[${this.sourceContext}]`, message, context || "", error || "");
    }

    // Send LOG message to background (fire-and-forget)
    const logMessage = {
      type: "LOG" as const,
      level,
      message,
      context,
      error: error?.message,
      stack: error?.stack,
      source: this.sourceContext,
      timestamp: Date.now(),
    };

    // Use runtime.sendMessage for fire-and-forget messaging
    this.runtime.sendMessage(logMessage).catch((sendError) => {
      // Fallback to console if messaging fails
      if (this.options?.fallbackToConsole !== false) {
        console[level](`[${this.sourceContext}] ${message}`, context || "", error || "");
        console.warn("Failed to send log message:", sendError);
      }
    });
  }
}
